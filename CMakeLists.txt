cmake_minimum_required(VERSION 3.10)
project(rtti CXX)

set(CMAKE_COLOR_MAKEFILE ON)
set(CMAKE_VERBOSE_MAKEFILE OFF)

# Build options
option(ENABLE_DOCS             "Enable documentation target"                OFF)
option(ENABLE_CODE_COVERAGE    "Enable code coverage generation"            OFF)
option(ENABLE_CODE_ANALYSIS    "Enable static code analysis"                OFF)
option(ENABLE_CPPCHECK         "Enable cppcheck for static code analysis"   OFF)
option(ENABLE_CLANG_TIDY       "Enable clang-tidy for static code analysis" OFF)
option(BUILD_TESTS             "Build unittest binary"                      ON)
option(BUILD_BENCHMARK         "Build benchmark binary"                     ON)

# CXX compilation options
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS_DEBUG   "${CMAKE_CXX_FLAGS} -O0 -ggdb")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS} -O3")

# CMake module path
list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

# Vendor installation path
set(EXTERNAL_INSTALL_DIR ${PROJECT_BINARY_DIR}/external)
include_directories(${EXTERNAL_INSTALL_DIR}/include)
link_directories(${EXTERNAL_INSTALL_DIR}/lib)

# Code formatting
include(clang-format)

# Code coverage generation
if(ENABLE_CODE_COVERAGE)
    include(code-coverage)
    append_coverage_compiler_flags()
endif()

# Static code analysis
if(ENABLE_CODE_ANALYSIS)
    if (ENABLE_CPPCHECK)
        message(STATUS "Attempting to find code analysis tools:")
        find_program(CMAKE_CXX_CPPCHECK NAMES cppcheck)
        if(CMAKE_CXX_CPPCHECK)
            message(STATUS "- Found `cppcheck`")
            list(APPEND CMAKE_CXX_CPPCHECK
                "--enable=all"
                "--suppress=missingIncludeSystem"
                "--inline-suppr"
                "--force"
                "--suppressions-list=${CMAKE_SOURCE_DIR}/.cppcheck-suppressions"
            )
        endif()
    endif()

    if (ENABLE_CLANG_TIDY)
        find_program(CMAKE_CXX_CLANG_TIDY NAMES clang-tidy)
        if(CMAKE_CXX_CPPCHECK)
            message(STATUS "- Found `clang-tidy`")
            list(APPEND CMAKE_CXX_CLANG_TIDY
                "-header-filter=${CMAKE_SOURCE_DIR}/include"
                "-checks=*"
            )
        endif()
    endif()
endif()

# Library
set(SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/include/rtti.hh)
add_library(rtti INTERFACE)
target_include_directories(rtti INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/include)
clang_format(rtti ${SOURCES})

# Configure install targets
include(GNUInstallDirs)
install(DIRECTORY include/
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    FILES_MATCHING PATTERN "*.hh"
)

# Documentation
if (ENABLE_DOCS)
    find_package(Doxygen REQUIRED dot mscgen dia)

    set(DOXYGEN_GENERATE_HTML YES)
    set(DOXYGEN_GENERATE_MAN NO)

    doxygen_add_docs(docs
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        COMMENT "Generate documentation") 
endif()

# Testing
if (BUILD_TESTS)
    enable_testing()
    include(googletest)
    add_subdirectory(tests)
endif()

# Benchmark
if (BUILD_BENCHMARK)
    include(googlebenchmark)
    add_subdirectory(benchmark)
endif()
