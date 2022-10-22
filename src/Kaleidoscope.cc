#include "KaleidoscopeJIT.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <cstdio>
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
    FOR,
    INCR,
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
    ASSIGN,
    ASIIC,
    UNKNOWN
};

std::string                         g_identifier_string;
double                              g_number_val;
Token_t                             g_current_token_type;
std::map<std::string, llvm::Value*> g_named_values;

const std::map<char, Token_t> g_char_token = {
    {'(', Token_t::LEFT_PAREN}, {')', Token_t::RIGHT_PAREM}, {',', Token_t::COMMA},     {'+', Token_t::ADD},        {'-', Token_t::SUB},
    {'*', Token_t::MUL},        {'/', Token_t::DIV},         {'<', Token_t::LESS_THAN}, {'>', Token_t::GREAT_THAN}, {'=', Token_t::ASSIGN}};

const std::map<std::string, Token_t> g_keyword_token = {{"if", Token_t::IF},    {"then", Token_t::THEN},     {"else", Token_t::ELSE},
                                                        {"def", Token_t::DEF},  {"extern", Token_t::EXTERN}, {"for", Token_t::FOR},
                                                        {"incr", Token_t::INCR}};

const std::map<Token_t, int> g_binop_precedence = {{Token_t::LESS_THAN, 10}, {Token_t::GREAT_THAN, 10}, {Token_t::ADD, 20},
                                                   {Token_t::SUB, 20},       {Token_t::MUL, 30},        {Token_t::DIV, 30}};

static llvm::ExitOnError ExitOnErr;
llvm::Function*          GetFunction(const std::string& func_name);

static std::unique_ptr<llvm::LLVMContext>                 g_llvm_context;
static std::unique_ptr<llvm::IRBuilder<>>                 g_ir_builder;
static std::unique_ptr<llvm::Module>                      g_module;
static std::unique_ptr<llvm::legacy::FunctionPassManager> g_fpm;
static std::unique_ptr<llvm::orc::KaleidoscopeJIT>        g_jit;

Token_t GetToken() {
    static char last_char = ' ';
    while (std::isspace(last_char) && last_char != '\n') {
        last_char = getchar();
    }

    if (g_char_token.find(last_char) != g_char_token.end()) {
        const char saved_last_char = last_char;
        g_identifier_string        = saved_last_char;
        last_char                  = getchar();
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
    virtual ~ExprAST()             = default;
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
        return llvm::ConstantFP::get(*g_llvm_context, llvm::APFloat(m_val));
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
        if (g_named_values.find(m_name) == g_named_values.end()) {
            return nullptr;
        }
        return g_named_values.at(m_name);
    }
};

class BinaryExprAST : public ExprAST {
private:
    Token_t                  m_op;
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
                return g_ir_builder->CreateFAdd(lhs, rhs, "addtmp");
            case Token_t::SUB:
                return g_ir_builder->CreateFSub(lhs, rhs, "subtmp");
            case Token_t::MUL:
                return g_ir_builder->CreateFMul(lhs, rhs, "multmp");
            case Token_t::DIV:
                return g_ir_builder->CreateFDiv(lhs, rhs, "divtmp");
            case Token_t::LESS_THAN: {
                llvm::Value* tmp = g_ir_builder->CreateFCmpULT(lhs, rhs, "cmptmp");
                return g_ir_builder->CreateUIToFP(tmp, llvm::Type::getDoubleTy(*g_llvm_context), "bool_less_than");
            }
            case Token_t::GREAT_THAN: {
                llvm::Value* tmp = g_ir_builder->CreateFCmpULT(rhs, lhs, "cmptmp");
                return g_ir_builder->CreateUIToFP(tmp, llvm::Type::getDoubleTy(*g_llvm_context), "bool_great_than");
            }
            default:
                break;
        }
        return nullptr;
    }
};

class CallExprAST : public ExprAST {
private:
    std::string                           m_callee;
    std::vector<std::unique_ptr<ExprAST>> m_args;

public:
    // TODO: 这里是不是右值传过去
    CallExprAST(std::string&& callee, std::vector<std::unique_ptr<ExprAST>>&& args)
        : m_callee(std::move(callee))
        , m_args(std::move(args)) {
    }
    llvm::Value* CodeGen() override {
        // std::cout << __func__ << " m_callee:" << m_callee << std::endl;
        auto callee = GetFunction(m_callee);
        if (nullptr == callee) {
            fprintf(stderr, "Unknown function referenced");
            return nullptr;
        }

        if (callee->arg_size() != m_args.size()) {
            fprintf(stderr, "Incorrect # arguments passed");
            return nullptr;
        }

        std::vector<llvm::Value*> args;
        for (auto& arg_expr : m_args) {
            args.push_back(arg_expr->CodeGen());
        }
        return g_ir_builder->CreateCall(callee, args, std::string("__calleetmp_" + m_callee + "__").c_str());
    }
};

class IfExprAST : public ExprAST {
private:
    std::unique_ptr<ExprAST> m_cond;
    std::unique_ptr<ExprAST> m_then_expr;
    std::unique_ptr<ExprAST> m_else_expr;

public:
    IfExprAST(std::unique_ptr<ExprAST> cond, std::unique_ptr<ExprAST> then_expr, std::unique_ptr<ExprAST> else_expr)
        : m_cond(std::move(cond))
        , m_then_expr(std::move(then_expr))
        , m_else_expr(std::move(else_expr)) {
    }

    llvm::Value* CodeGen() override {
        llvm::Value* cond_val = m_cond->CodeGen();
        // Convert condition to a bool by comparing non-equal to 0.0
        cond_val = g_ir_builder->CreateFCmpONE(cond_val, llvm::ConstantFP::get(*g_llvm_context, llvm::APFloat(0.0)), "ifcond");

        llvm::Function*   func        = g_ir_builder->GetInsertBlock()->getParent();
        llvm::BasicBlock* then_block  = llvm::BasicBlock::Create(*g_llvm_context, "then", func);
        llvm::BasicBlock* else_block  = llvm::BasicBlock::Create(*g_llvm_context, "else");
        llvm::BasicBlock* final_block = llvm::BasicBlock::Create(*g_llvm_context, "ifcont");

        g_ir_builder->CreateCondBr(cond_val, then_block, else_block);

        g_ir_builder->SetInsertPoint(then_block);
        llvm::Value* then_val = m_then_expr->CodeGen();
        g_ir_builder->CreateBr(final_block);
        then_block = g_ir_builder->GetInsertBlock();

        func->getBasicBlockList().push_back(else_block);
        g_ir_builder->SetInsertPoint(else_block);
        llvm::Value* else_val = m_else_expr->CodeGen();
        g_ir_builder->CreateBr(final_block);
        else_block = g_ir_builder->GetInsertBlock();

        func->getBasicBlockList().push_back(final_block);
        g_ir_builder->SetInsertPoint(final_block);

        llvm::PHINode* pn = g_ir_builder->CreatePHI(llvm::Type::getDoubleTy(*g_llvm_context), 2, "iftmp");
        pn->addIncoming(then_val, then_block);
        pn->addIncoming(else_val, else_block);
        return pn;
    }
};

class ForExprAST : public ExprAST {
private:
    std::string              m_var_name;
    std::unique_ptr<ExprAST> m_start;
    std::unique_ptr<ExprAST> m_end;
    std::unique_ptr<ExprAST> m_step;
    std::unique_ptr<ExprAST> m_loop_body;

public:
    ForExprAST(
        const std::string& var_name, std::unique_ptr<ExprAST> start, std::unique_ptr<ExprAST> end, std::unique_ptr<ExprAST> step,
        std::unique_ptr<ExprAST> loop_body)
        : m_var_name(var_name)
        , m_start(std::move(start))
        , m_end(std::move(end))
        , m_step(std::move(step))
        , m_loop_body(std::move(loop_body)) {
    }

    /*
    define double @__anonymous_expr_fixed__() {
        entry:
            br label %loop

        loop:                                             ; preds = %loop, %entry
            %i = phi double [ 1.000000e+00, %entry ], [ %next_val, %loop ]
            %cmptmp = fcmp ult double %i, 1.000000e+01
            br i1 %cmptmp, label %body, label %after_loop
        body:
            %__calleetmp_putchard__ = call double @putchard(double 5.600000e+01)
            %next_val = fadd double %i, 1.000000e+00
            br label %loop
        after_loop:                                       ; preds = %loop
            ret double 0.000000e+00
    }
    */
    llvm::Value* CodeGen() override {
        // TODO
        llvm::Value* init_val = m_start->CodeGen();
        if (nullptr == init_val) {
            fprintf(stderr, "failed to generate code of for star body\n");
            return nullptr;
        }

        llvm::Function* cur_func = g_ir_builder->GetInsertBlock()->getParent();

        // 预创建所有用到的四个标签
        llvm::BasicBlock* entry_block = g_ir_builder->GetInsertBlock();
        llvm::BasicBlock* loop_block  = llvm::BasicBlock::Create(*g_llvm_context, "loop", cur_func);
        llvm::BasicBlock* body_block  = llvm::BasicBlock::Create(*g_llvm_context, "body", cur_func);
        llvm::BasicBlock* after_loop  = llvm::BasicBlock::Create(*g_llvm_context, "after_loop", cur_func);

        // 指定代码插入点为 entry 标签处
        g_ir_builder->SetInsertPoint(entry_block);
        // 无条件跳转到 loop 标签
        g_ir_builder->CreateBr(loop_block);

        // 指定代码插入点为 loop 标签处
        g_ir_builder->SetInsertPoint(loop_block);
        llvm::PHINode* var = g_ir_builder->CreatePHI(llvm::Type::getDoubleTy(*g_llvm_context), 2, m_var_name);
        var->addIncoming(init_val, entry_block);

        bool         is_existed_var_name      = g_named_values.find(m_var_name) == g_named_values.end();
        llvm::Value* saved_the_same_named_var = is_existed_var_name ? g_named_values[m_var_name] : nullptr;
        g_named_values[m_var_name]            = var;

        llvm::Value* end_cond = m_end->CodeGen();
        if (nullptr == end_cond) {
            fprintf(stderr, "failed to generate code of for loop end\n");
            return nullptr;
        }

        // Convert condition to a bool by comparing non-equal to 0.0
        end_cond = g_ir_builder->CreateFCmpONE(end_cond, llvm::ConstantFP::get(*g_llvm_context, llvm::APFloat(0.0)), "loop_end_cond");
        g_ir_builder->CreateCondBr(end_cond, body_block, after_loop);

        // 指定代码插入点为 body 标签处
        g_ir_builder->SetInsertPoint(body_block);

        if (nullptr == m_loop_body->CodeGen()) {
            fprintf(stderr, "failed to generate code of for loop body\n");
            return nullptr;
        }

        llvm::Value* step_val = m_step->CodeGen();
        if (nullptr == step_val) {
            fprintf(stderr, "failed to generate code of for loop step\n");
            return nullptr;
        }

        llvm::Value*      next_val                  = g_ir_builder->CreateFAdd(var, step_val, "next_val");
        llvm::BasicBlock* generating_next_val_block = g_ir_builder->GetInsertBlock();
        g_ir_builder->CreateBr(loop_block);

        var->addIncoming(next_val, generating_next_val_block);

        // 指定代码插入点为 after_loop 标签处
        g_ir_builder->SetInsertPoint(after_loop);
        if (is_existed_var_name) {
            g_named_values[m_var_name] = saved_the_same_named_var;
        }
        return llvm::Constant::getNullValue(llvm::Type::getDoubleTy(*g_llvm_context));
    }
};

class PrototypeAST {
private:
    std::string              m_name;
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
        std::vector<llvm::Type*> double_type_args(m_args.size(), llvm::Type::getDoubleTy(*g_llvm_context));
        llvm::FunctionType*      function_type = llvm::FunctionType::get(llvm::Type::getDoubleTy(*g_llvm_context), double_type_args, false);
        llvm::Function*          func  = llvm::Function::Create(function_type, llvm::Function::ExternalLinkage, m_name, g_module.get());
        int                      index = 0;
        for (auto& arg : func->args()) {
            arg.setName(m_args[index++]);
        }
        return func;
    }
};

static std::map<std::string, std::unique_ptr<PrototypeAST>> g_function_protos;

class FunctionAST {
private:
    std::unique_ptr<PrototypeAST> m_proto;
    std::unique_ptr<ExprAST>      m_body;

public:
    FunctionAST(std::unique_ptr<PrototypeAST>& proto, std::unique_ptr<ExprAST>& body)
        : m_proto(std::move(proto))
        , m_body(std::move(body)) {
    }

    llvm::Value* CodeGen() {
        auto& cur_proto = *m_proto;
        g_function_protos.emplace(cur_proto.GetName(), std::move(m_proto));
        llvm::Function* func = GetFunction(cur_proto.GetName());
        if (nullptr == func) {
            fprintf(stderr, "Unknown function referenced");
            return nullptr;
        }

        llvm::BasicBlock* block = llvm::BasicBlock::Create(*g_llvm_context, "entry", func);
        g_ir_builder->SetInsertPoint(block);
        // 预设了 Kaleidoscope 的 VariableExpr 只存在于函数内对函数参数的引用
        g_named_values.clear();
        for (llvm::Value& arg : func->args()) {
            g_named_values.emplace(arg.getName(), &arg);
        }

        llvm::Value* ret_val = m_body->CodeGen();
        if (ret_val) {
            g_ir_builder->CreateRet(ret_val);
            llvm::verifyFunction(*func);
            // TODO: for 循环会崩溃在这里
            g_fpm->run(*func);
            return func;
        }

        func->eraseFromParent();
        return nullptr;
    }
};

llvm::Function* GetFunction(const std::string& func_name) {
    auto func = g_module->getFunction(func_name);
    if (func) {
        return func;
    }
    auto func_iterator = g_function_protos.find(func_name);
    if (func_iterator != g_function_protos.end()) {
        return func_iterator->second->CodeGen();
    }
    return nullptr;
}

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

std::unique_ptr<ExprAST> ParseIfExpr() {
    GetNextToken();
    std::unique_ptr<ExprAST> cond = ParseExpression();
    GetNextToken();
    std::unique_ptr<ExprAST> then_expr = ParseExpression();
    GetNextToken();
    std::unique_ptr<ExprAST> else_expr = ParseExpression();
    return std::make_unique<IfExprAST>(std::move(cond), std::move(then_expr), std::move(else_expr));
}

std::unique_ptr<ForExprAST> ParseForExpr();

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
        case Token_t::IF:
            return ParseIfExpr();
        case Token_t::FOR:
            return ParseForExpr();
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
    auto expr  = ParseExpression();
    return std::make_unique<FunctionAST>(proto, expr);
}

// extern ::= extern prototype
std::unique_ptr<PrototypeAST> ParseExtern() {
    GetNextToken();
    return ParsePrototype();
}

std::unique_ptr<ForExprAST> ParseForExpr() {
    GetNextToken();
    if (g_current_token_type != Token_t::IDENTIFIER) {
        fprintf(stderr, "Expected an identifier after 'for'\n");
        return nullptr;
    }

    std::string var_name = g_identifier_string;
    GetNextToken();
    if (g_current_token_type != Token_t::ASSIGN) {
        fprintf(stderr, "Expected '=' after 'for'\n");
        return nullptr;
    }

    GetNextToken();
    auto start = ParseExpression();
    if (nullptr == start) {
        fprintf(stderr, "invalid start in for loop\n");
        return nullptr;
    }

    // GetNextToken();
    if (g_current_token_type != Token_t::COMMA) {
        fprintf(stderr, "Expected an comma after start in for loop\n");
        return nullptr;
    }

    GetNextToken();
    auto end = ParseExpression();
    if (nullptr == end) {
        fprintf(stderr, "invalid end condition in for loop\n");
        return nullptr;
    }

    // GetNextToken();
    if (g_current_token_type != Token_t::COMMA) {
        fprintf(stderr, "Expected an comma after condition in for loop\n");
        return nullptr;
    }

    GetNextToken();
    auto step = ParseExpression();
    if (nullptr == step) {
        fprintf(stderr, "invalid step in for loop\n");
        return nullptr;
    }

    // GetNextToken();
    if (g_current_token_type != Token_t::INCR) {
        fprintf(stderr, "Expected an incr after step in for loop\n");
        return nullptr;
    }

    GetNextToken();
    auto loop_body = ParseExpression();
    if (loop_body == step) {
        fprintf(stderr, "invalid loop body in for loop\n");
        return nullptr;
    }

    return std::make_unique<ForExprAST>(var_name, std::move(start), std::move(end), std::move(step), std::move(loop_body));
}

// toplevelexpr ::= expression
std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
    auto proto = std::make_unique<PrototypeAST>("__anonymous_expr__", std::vector<std::string>{});
    auto expr  = ParseExpression();
    return std::make_unique<FunctionAST>(proto, expr);
}

static void InitializeModule() {
    g_llvm_context = std::make_unique<llvm::LLVMContext>();
    g_module       = std::make_unique<llvm::Module>("Kaleidoscope JIT", *g_llvm_context);
#ifdef USE_JIT
    g_module->setDataLayout(g_jit->getDataLayout());
#endif
    g_ir_builder = std::make_unique<llvm::IRBuilder<>>(*g_llvm_context);

    g_fpm = std::make_unique<llvm::legacy::FunctionPassManager>(g_module.get());
    g_fpm->add(llvm::createInstructionCombiningPass());
    g_fpm->add(llvm::createReassociatePass());
    g_fpm->add(llvm::createGVNPass());
    g_fpm->add(llvm::createCFGSimplificationPass());
    g_fpm->doInitialization();
}

static void HandleDefination() {
    auto pd_ast = ParseDefinition();
    std::cout << "parsed a function definition" << std::endl;
    pd_ast->CodeGen()->print(llvm::outs());
    std::cout << std::endl;
#ifdef USE_JIT
    // 定义的函数注册至 JIT，并注册新的模块与优化器
    // 否则在 JIT 模式下第二次调用函数会出现未定义的错误
    ExitOnErr(g_jit->addModule(llvm::orc::ThreadSafeModule(std::move(g_module), std::move(g_llvm_context))));
    InitializeModule();
#endif
}

static void HandleTopLevelExpression() {
    auto ptle_ast = ParseTopLevelExpr();
    std::cout << "parsed a top level expr" << std::endl;
    auto ptle_ast_code = ptle_ast->CodeGen();
    if (ptle_ast_code) {
        ptle_ast_code->print(llvm::outs());
#ifdef USE_JIT
        // Create a ResourceTracker to track JIT's memory allocated to our
        // anonymous expression -- that way we can free it after executing.
        auto resource_tracker = g_jit->getMainJITDylib().createResourceTracker();
        auto tsm              = llvm::orc::ThreadSafeModule(std::move(g_module), std::move(g_llvm_context));
        ExitOnErr(g_jit->addModule(std::move(tsm), resource_tracker));
        InitializeModule();
        auto symbol    = ExitOnErr(g_jit->lookup("__anonymous_expr__"));
        double (*fp)() = reinterpret_cast<double (*)()>(symbol.getAddress());
        std::cout << "JIT evaluated to: " << fp() << std::endl;
        ExitOnErr(resource_tracker->remove());
#else
        // 解决非JIT模式下匿名函数覆盖问题
        static_cast<llvm::Function*>(ptle_ast_code)->eraseFromParent();
#endif
    } else {
        // GetNextToken();
        std::cout << "parse top level expr failed" << std::endl;
    }
}

static void HandleExtern() {
    auto pe_ast = ParseExtern();
    std::cout << "parsed a extern" << std::endl;
    auto pe_ast_code = pe_ast->CodeGen();
    if (pe_ast_code) {
        pe_ast_code->print(llvm::outs());
        std::cout << std::endl;
        g_function_protos.emplace(pe_ast->GetName(), std::move(pe_ast));
    } else {
        std::cout << "parse extern expr failed" << std::endl;
    }
}

static void HandleForExpression() {
    auto for_ast = ParseForExpr();
    std::cout << "parsed a for loop" << std::endl;
    auto for_ast_code = for_ast->CodeGen();
    if (for_ast_code) {
        for_ast_code->print(llvm::outs());
    } else {
        std::cerr << "failed to generate IR for 'for' loop" << std::endl;
    }
}

static void MainLoop() {
    while (true) {
        std::cout << "\033[31mReady > \033[0m";
        GetNextToken();
        switch (g_current_token_type) {
            case Token_t::END_OF_FILE:
                return;
            case Token_t::DEF: {
                HandleDefination();
                break;
            }
            case Token_t::EXTERN: {
                HandleExtern();
                break;
            }
            // case Token_t::FOR: {
            //     HandleForExpression();
            //     break;
            // }
            case Token_t::ASIIC: {
                // std::cout << "parsed a ASIIC: " << g_identifier_string << std::endl;
                break;
            }
            default: {
                HandleTopLevelExpression();
                break;
            }
        }
        g_identifier_string  = "";
        g_current_token_type = Token_t::END_OF_FILE;
    }
}

extern "C" double putchard(double X) {
    fputc((char)X, stdout);
    std::cout << std::endl;
    return 0;
}

extern "C" double printd(double X) {
    fprintf(stdout, "%f\n", X);
    return 0;
}

int main() {
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();
    llvm::InitializeNativeTargetAsmParser();
#ifdef USE_JIT
    g_jit = ExitOnErr(llvm::orc::KaleidoscopeJIT::Create());
    std::cout << "JIT created" << std::endl;
#endif
    InitializeModule();

    MainLoop();
    return 0;
}
