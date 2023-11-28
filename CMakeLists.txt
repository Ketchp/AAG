cmake_minimum_required(VERSION 3.20)
project(AAG1)
project(AAG2)

set(CMAKE_CXX_STANDARD 20)

add_compile_options(-Wall -Wextra -Wpedantic)

# Add executable target with source files listed in SOURCE_FILES variable
#add_executable(AGG src/NKA2DKA.cpp)
#add_executable(AGG src/aag0.cpp)
#add_executable(AGG src/ka_transformations.cpp)
add_executable(AGG1 src/aag1.cpp)
add_executable(AGG2 src/aag2.cpp)
