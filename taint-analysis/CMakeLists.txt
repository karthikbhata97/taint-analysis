include(FetchContent)

# Fetch spdlog
FetchContent_Declare(
        spdlog
        GIT_REPOSITORY https://github.com/gabime/spdlog.git
        GIT_TAG v1.12.0
)
FetchContent_MakeAvailable(spdlog)

include_directories(SYSTEM "${spdlog_SOURCE_DIR}/include")

llvm_map_components_to_libnames(llvm_libs bitwriter core ipo irreader instcombine instrumentation target linker analysis scalaropts support )
file (GLOB SOURCES
   *.cpp
   k-alias-analysis/kaa.cpp
)

add_executable(taint-analysis ${SOURCES})

target_link_libraries(taint-analysis ${SVF_LIB} ${llvm_libs} ${SVF_CORE})

set_target_properties(taint-analysis PROPERTIES
                       RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
