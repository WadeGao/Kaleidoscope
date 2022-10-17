#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Scalar/GVN.h>

#include <cstddef>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

enum class Token_t {
    END_OF_FILE,
    IF,
    THEN,
    ELSE,
    DEF,
    EXTERN,
    IDENTIFIER,
    NUMBER,
    LEFT_PAREN,
    RIGHT_PAREM,
    COMMA,
    LESS_THAN,
    GREAT_THAN,
    ADD,
    SUB,
    MUL,
    DIV,
    ASIIC,
    UNKNOWN
};

std::string g_identifier_string;
double g_number_val;
Token_t g_current_token_type;

const std::map<char, Token_t> g_char_token = {{'(', Token_t::LEFT_PAREN}, {')', Token_t::RIGHT_PAREM}, {',', Token_t::COMMA},
                                              {'+', Token_t::ADD},        {'-', Token_t::SUB},         {'*', Token_t::MUL},
                                              {'/', Token_t::DIV},        {'<', Token_t::LESS_THAN},   {'>', Token_t::GREAT_THAN}};

const std::map<std::string, Token_t> g_keyword_token = {
    {"if", Token_t::IF}, {"then", Token_t::THEN}, {"else", Token_t::ELSE}, {"def", Token_t::DEF}, {"extern", Token_t::EXTERN}};

const std::map<Token_t, int> g_binop_precedence = {{Token_t::LESS_THAN, 10}, {Token_t::GREAT_THAN, 10}, {Token_t::ADD, 20},
                                                   {Token_t::SUB, 20},       {Token_t::MUL, 30},        {Token_t::DIV, 30}};

llvm::LLVMContext g_llvm_context;
llvm::IRBuilder<> g_ir_builder(g_llvm_context);
llvm::Module g_module("Kaleidoscope", g_llvm_context);
std::map<std::string, llvm::Value*> g_named_values;

Token_t GetToken() {
    static char last_char = ' ';
    while (std::isspace(last_char) && last_char != '\n') {
        last_char = getchar();
    }

    if (g_char_token.find(last_char) != g_char_token.end()) {
        const char saved_last_char = last_char;
        g_identifier_string = saved_last_char;
        last_char = getchar();
        return g_char_token.at(saved_last_char);
    }

    if (std::isalpha(last_char)) {
        g_identifier_string = last_char;
        while (std::isalnum(last_char = getchar())) {
            g_identifier_string += last_char;
        }

        if (g_keyword_token.find(g_identifier_string) != g_keyword_token.end()) {
            return g_keyword_token.at(g_identifier_string);
        }

        return Token_t::IDENTIFIER;
    }

    if (std::isdigit(last_char) || last_char == '.') {
        std::string num_str;
        do {
            num_str += last_char;
            last_char = getchar();
        } while (std::isdigit(last_char) || last_char == '.');
        g_number_val = strtod(num_str.c_str(), nullptr);
        return Token_t::NUMBER;
    }

    if (last_char == '#') {
        do {
            last_char = getchar();
        } while (last_char != EOF && last_char != '\n' && last_char != '\r');
        if (last_char != EOF) {
            return GetToken();
        }
    }

    if (last_char == EOF) {
        return Token_t::END_OF_FILE;
    }

    g_identifier_string = last_char;
    // last_char = getchar();
    last_char = ' ';
    return Token_t::ASIIC;
}

Token_t GetNextToken() {
    return g_current_token_type = GetToken();
}

class ExprAST {
public:
    virtual ~ExprAST() = default;
    virtual llvm::Value* CodeGen() = 0;
};

class NumberExprAST : public ExprAST {
private:
    double m_val;

public:
    NumberExprAST(double val)
        : m_val(val) {
    }
    llvm::Value* CodeGen() override {
        return llvm::ConstantFP::get(g_llvm_context, llvm::APFloat(m_val));
    }
};

class VarExprAST : public ExprAST {
private:
    std::string m_name;

public:
    VarExprAST(const std::string& name)
        : m_name(name) {
    }
    llvm::Value* CodeGen() override {
        return g_named_values.at(m_name);
    }
};

class BinaryExprAST : public ExprAST {
private:
    Token_t m_op;
    std::unique_ptr<ExprAST> m_lhs;
    std::unique_ptr<ExprAST> m_rhs;

public:
    BinaryExprAST(const Token_t op, std::unique_ptr<ExprAST> lhs, std::unique_ptr<ExprAST> rhs)
        : m_op(op)
        , m_lhs(std::move(lhs))
        , m_rhs(std::move(rhs)) {
    }

    llvm::Value* CodeGen() override {
        llvm::Value* lhs = m_lhs->CodeGen();
        llvm::Value* rhs = m_rhs->CodeGen();
        switch (m_op) {
            case Token_t::ADD:
                return g_ir_builder.CreateFAdd(lhs, rhs, "addtmp");
            case Token_t::SUB:
                return g_ir_builder.CreateFSub(lhs, rhs, "subtmp");
            case Token_t::MUL:
                return g_ir_builder.CreateFMul(lhs, rhs, "multmp");
            case Token_t::DIV:
                return g_ir_builder.CreateFDiv(lhs, rhs, "divtmp");
            case Token_t::LESS_THAN: {
                llvm::Value* tmp = g_ir_builder.CreateFCmpULT(lhs, rhs, "cmptmp");
                return g_ir_builder.CreateUIToFP(tmp, llvm::Type::getDoubleTy(g_llvm_context), "booltmp");
            }
            default:
                break;
        }
        return nullptr;
    }
};

class CallExprAST : public ExprAST {
private:
    std::string m_callee;
    std::vector<std::unique_ptr<ExprAST>> m_args;

public:
    CallExprAST(std::string&& callee, std::vector<std::unique_ptr<ExprAST>>&& args)
        : m_callee(std::move(callee))
        , m_args(std::move(args)) {
    }
    llvm::Value* CodeGen() override {
        llvm::Function* callee = g_module.getFunction(m_callee);
        std::vector<llvm::Value*> args;
        for (auto& arg_expr : m_args) {
            args.push_back(arg_expr->CodeGen());
        }
        return g_ir_builder.CreateCall(callee, args, "calleetmp");
    }
};

class PrototypeAST {
private:
    std::string m_name;
    std::vector<std::string> m_args;

public:
    PrototypeAST(std::string& name, std::vector<std::string>& args)
        : m_name(name)
        , m_args(args) {
    }

    PrototypeAST(std::string&& name, std::vector<std::string>&& args)
        : m_name(std::move(name))
        , m_args(std::move(args)) {
    }

    const std::string& GetName() const {
        return m_name;
    }

    llvm::Function* CodeGen() {
        std::vector<llvm::Type*> doubles(m_args.size(), llvm::Type::getDoubleTy(g_llvm_context));
        llvm::FunctionType* function_type = llvm::FunctionType::get(llvm::Type::getDoubleTy(g_llvm_context), doubles, false);
        llvm::Function* func = llvm::Function::Create(function_type, llvm::Function::ExternalLinkage, m_name, &g_module);
        int index = 0;
        for (auto& arg : func->args()) {
            arg.setName(m_args[index++]);
        }
        return func;
    }
};

class FunctionAST {
private:
    std::unique_ptr<PrototypeAST> m_proto;
    std::unique_ptr<ExprAST> m_body;

public:
    FunctionAST(std::unique_ptr<PrototypeAST>& proto, std::unique_ptr<ExprAST>& body)
        : m_proto(std::move(proto))
        , m_body(std::move(body)) {
    }

    llvm::Value* CodeGen() {
        llvm::Function* func = g_module.getFunction(m_proto->GetName());
        if (nullptr == func) {
            func = m_proto->CodeGen();
        }
        llvm::BasicBlock* block = llvm::BasicBlock::Create(g_llvm_context, "entry", func);
        g_ir_builder.SetInsertPoint(block);
        g_named_values.clear();
        for (llvm::Value& arg : func->args()) {
            // g_named_values[arg.getName()] = &arg;
            g_named_values.emplace(arg.getName(), &arg);
        }

        llvm::Value* ret_val = m_body->CodeGen();
        g_ir_builder.CreateRet(ret_val);
        llvm::verifyFunction(*func);
        return func;
    }
};

std::unique_ptr<ExprAST> ParseNumberExpr() {
    auto res = std::make_unique<NumberExprAST>(g_number_val);
    // TODO: 输入 1+2-3*4，到了 4 无法知道是否结束
    GetNextToken();
    return std::move(res);
}

std::unique_ptr<ExprAST> ParseExpression();

// parenexpr ::= ( expression )
std::unique_ptr<ExprAST> ParseParenExpr() {
    GetNextToken();
    auto expr = ParseExpression();
    GetNextToken();
    return expr;
}

// identifierexpr ::= identifier | identifier ( expression1, expression2, ... )
std::unique_ptr<ExprAST> ParseIdentifierExpr() {
    std::string id = g_identifier_string;
    // TODO: 单独输入 y，无法知道是否结束
    GetNextToken();
    if (g_current_token_type != Token_t::LEFT_PAREN) {
        return std::make_unique<VarExprAST>(id);
    }

    // eat '('
    GetNextToken();
    std::vector<std::unique_ptr<ExprAST>> args;
    while (g_current_token_type != Token_t::RIGHT_PAREM) {
        args.push_back(ParseExpression());
        if (g_current_token_type == Token_t::RIGHT_PAREM) {
            break;
        } else {
            // eat ','
            GetNextToken();
        }
    }
    GetNextToken();
    return std::make_unique<CallExprAST>(std::move(id), std::move(args));
}

// primary
//   ::= identifierexpr
//   ::= numberexpr
//   ::= parenexpr
std::unique_ptr<ExprAST> ParsePrimary() {
    switch (g_current_token_type) {
        case Token_t::IDENTIFIER:
            return ParseIdentifierExpr();
        case Token_t::NUMBER:
            return ParseNumberExpr();
        case Token_t::LEFT_PAREN:
            return ParseParenExpr();
        default:
            break;
    }
    return nullptr;
}

int GetTokenPrecedence() {
    auto it = g_binop_precedence.find(g_current_token_type);
    return it == g_binop_precedence.end() ? -1 : it->second;
}

// parse lhs, [binop primary] [binop primary] ...
std::unique_ptr<ExprAST> ParseBinOpRhs(int min_precedence, std::unique_ptr<ExprAST> lhs) {
    for (;;) {
        int cur_precedence = GetTokenPrecedence();
        if (cur_precedence < min_precedence) {
            return lhs;
        }

        Token_t binop = g_current_token_type;
        GetNextToken();
        auto rhs = ParsePrimary();

        // (lhs binop rhs) binop unparsed
        // lhs binop (rhs binop unparsed)
        int next_precedence = GetTokenPrecedence();
        if (cur_precedence < next_precedence) {
            rhs = ParseBinOpRhs(cur_precedence + 1, std::move(rhs));
        }
        lhs = std::make_unique<BinaryExprAST>(binop, std::move(lhs), std::move(rhs));
    }
    return nullptr;
}

std::unique_ptr<ExprAST> ParseExpression() {
    auto lhs = ParsePrimary();
    return ParseBinOpRhs(0, std::move(lhs));
}

// prototype ::= id ( id, id, ... )
std::unique_ptr<PrototypeAST> ParsePrototype() {
    std::string function_name = g_identifier_string;
    GetNextToken();
    std::vector<std::string> formal_args;
    while (GetNextToken() == Token_t::IDENTIFIER) {
        formal_args.push_back(g_identifier_string);
        // eat ',' or finish parse arg list
        if (GetNextToken() == Token_t::RIGHT_PAREM) {
            break;
        }
    }
    GetNextToken();
    return std::make_unique<PrototypeAST>(std::move(function_name), std::move(formal_args));
}

// defination ::= def prototype expression
std::unique_ptr<FunctionAST> ParseDefinition() {
    GetNextToken();
    auto proto = ParsePrototype();
    auto expr = ParseExpression();
    return std::make_unique<FunctionAST>(proto, expr);
}

// extern ::= extern prototype
std::unique_ptr<PrototypeAST> ParseExtern() {
    GetNextToken();
    return ParsePrototype();
}

// toplevelexpr ::= expression
std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
    auto expr = ParseExpression();
    auto proto = std::make_unique<PrototypeAST>("__anonymous_expr__", std::vector<std::string>{});
    return std::make_unique<FunctionAST>(proto, expr);
}

int main() {
    while (true) {
        std::cout << "\033[31mReady > \033[0m";
        GetNextToken();
        switch (g_current_token_type) {
            case Token_t::END_OF_FILE:
                return 0;
            case Token_t::DEF: {
                auto pd_ast = ParseDefinition();
                std::cout << "parsed a function definition" << std::endl;
                pd_ast->CodeGen()->print(llvm::errs());
                std::cerr << std::endl;
                break;
            }
            case Token_t::EXTERN: {
                auto pe_ast = ParseExtern();
                std::cout << "parsed a extern" << std::endl;
                pe_ast->CodeGen()->print(llvm::errs());
                std::cerr << std::endl;
                break;
            }
            case Token_t::ASIIC: {
                // std::cout << "parsed a ASIIC: " << g_identifier_string << std::endl;
                break;
            }
            default: {
                auto ptle_ast = ParseTopLevelExpr();
                std::cout << "parsed a top level expr" << std::endl;
                ptle_ast->CodeGen()->print(llvm::errs());
                std::cerr << std::endl;
                break;
            }
        }
        g_identifier_string = "";
        g_current_token_type = Token_t::END_OF_FILE;
    }
    return 0;
}
