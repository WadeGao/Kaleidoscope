set_languages("c11", "cxx17")
add_rules("mode.debug")

target("Kaleidoscope")
    set_kind("binary")
    set_targetdir("build")
    add_includedirs("include")
    add_files("src/**.cc")
    add_cxxflags("-g -v")
    add_defines("USE_JIT")
    add_defines("ENABLE_OPTIMIZER")
    if is_plat("macosx") then
        add_cxxflags("-stdlib=libc++ -fuse-ld=lld")
        add_includedirs("/opt/homebrew/opt/llvm/include")
        add_linkdirs("/opt/homebrew/opt/llvm/lib")
        add_links("LLVM")
        add_ldflags("--verbose")
    elseif is_plat("linux") then
        add_toolchains("gcc")
        add_includedirs("/usr/include/llvm")
        add_linkdirs("/usr/lib/llvm-15/lib")
        add_links("LLVM")
        add_ldflags("--verbose")
    else
    end
