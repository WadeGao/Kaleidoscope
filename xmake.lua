set_languages("c11", "cxx17")
add_rules("mode.debug")

target("Kaleidoscope")
    set_kind("binary")
    set_targetdir("build")
    add_includedirs("include")
    add_files("src/**.cc")
    add_cxxflags("-g -stdlib=libc++ -fuse-ld=lld -v")
    add_defines("USE_JIT")

    if is_plat("macosx") then
        add_includedirs("/opt/homebrew/opt/llvm/include")
        add_linkdirs("/opt/homebrew/opt/llvm/lib")
        add_links("LLVM")
        add_ldflags("--verbose")
    end

-- TODO: 使用JIT时，因为 g_module 重新创建，无法重复调用函数
