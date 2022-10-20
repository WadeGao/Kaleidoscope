set_languages("c11", "cxx17")
add_rules("mode.debug")

target("Kaleidoscope")
    set_kind("binary")
    set_targetdir("build")
    add_includedirs("include")
    add_files("src/**.cc")
    add_cxxflags("-g -stdlib=libc++ -fuse-ld=lld -v")
    if is_plat("macosx") then
        add_includedirs("/opt/homebrew/opt/llvm/include")
        add_linkdirs("/opt/homebrew/opt/llvm/lib")
        add_links("LLVM")
        add_ldflags("--verbose")
        -- add_defines("USE_JIT")
    end

-- TODO: 不使用JIT时，重复调用同一函数（不同参数），只会产生第一次调用生成的IR
    -- ？由于 LLVM 9.0 及以后版本不支持不同模块定义相同符号，因此 LLVM 9.0 及以后版本并不支持覆盖函数定义的能力。

-- TODO: 使用JIT时，因为 g_module 重新创建，无法重复调用函数
