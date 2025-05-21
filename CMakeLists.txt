cmake_minimum_required(VERSION 3.0.0)
project(IC3 VERSION 0.1.0 LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

#set(CMAKE_CXX_COMPILER /usr/bin/x86_64-linux-gnu-g++-11)
set(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -w")

include(CTest)
enable_testing()

include_directories(minisat aiger minisat/minisat/core minisat/minisat/mtl minisat/minisat/simp)

ADD_LIBRARY(kInd kInd.cpp Model.cpp aiger/aiger.c)
target_link_libraries(kInd PRIVATE -lz)
target_link_libraries(kInd PRIVATE ${CMAKE_SOURCE_DIR}/minisat/build/libminisat.a)

add_executable(kind main.cpp)

target_link_libraries(kind kInd)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
