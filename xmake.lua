set_languages("c11", "cxx17")
add_rules("mode.debug")

target("Kaleidoscope")
    set_kind("binary")
    set_targetdir("build")
    add_files("src/**.cc")
    add_cxxflags("-g -stdlib=libc++ -fuse-ld=lld -v")
    if is_plat("macosx") then
        add_includedirs("/opt/homebrew/Cellar/llvm/15.0.2/include")
        add_linkdirs("/opt/homebrew/Cellar/llvm/15.0.2/lib")
        add_links("LLVM-15")
        add_ldflags("--verbose")
    end
    