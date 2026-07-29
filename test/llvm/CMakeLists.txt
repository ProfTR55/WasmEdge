# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: Copyright The WasmEdge Authors

wasmedge_add_executable(wasmedgeLLVMCoreTests
  LinkerTest.cpp
  LLVMcoreTest.cpp
  NativeWriterTest.cpp
)

add_test(wasmedgeLLVMCoreTests wasmedgeLLVMCoreTests)

target_link_libraries(wasmedgeLLVMCoreTests
  PRIVATE
  wasmedgeTestSpec
  wasmedgeVM
)

target_compile_definitions(wasmedgeLLVMCoreTests PRIVATE
  WASMEDGE_LINKER_HAS_AARCH64=$<TARGET_PROPERTY:wasmedgeLLVM,WASMEDGE_LINKER_HAS_AARCH64>
  WASMEDGE_LINKER_HAS_LINUX_RELOCATIONS=$<TARGET_PROPERTY:wasmedgeLLVM,WASMEDGE_LINKER_HAS_LINUX_RELOCATIONS>
)

target_include_directories(wasmedgeLLVMCoreTests
  PRIVATE
  ${PROJECT_SOURCE_DIR}/lib/llvm
)

target_include_directories(wasmedgeLLVMCoreTests
  SYSTEM
  PRIVATE
  $<TARGET_PROPERTY:wasmedgeLLVM,INCLUDE_DIRECTORIES>
)

wasmedge_add_executable(wasmedgeLazyJITTests
  LazyJITTest.cpp
)

add_test(wasmedgeLazyJITTests wasmedgeLazyJITTests)

target_link_libraries(wasmedgeLazyJITTests
  PRIVATE
  wasmedgeVM
  GTest::gtest
)
