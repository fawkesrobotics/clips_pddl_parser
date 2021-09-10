cmake_minimum_required(VERSION 3.12)

project(
  clips_pddl_parser
  VERSION 0.9.0
	DESCRIPTION "Parse PDDL domains from within CLIPS")

include(GNUInstallDirs)

find_package(PddlParser REQUIRED)
find_package(spdlog REQUIRED)
include(FindPkgConfig)
pkg_check_modules(clipsmm REQUIRED IMPORTED_TARGET clipsmm-1.0)
add_library(clips_pddl_parser SHARED src/clips_pddl_parser.cpp src/precondition_visitor.cpp src/effect_visitor.cpp)
target_link_libraries(
  clips_pddl_parser PddlParser::pddl_parser
  PkgConfig::clipsmm spdlog::spdlog)
target_include_directories(
  clips_pddl_parser PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>)
target_compile_definitions(
  clips_pddl_parser PRIVATE SHAREDIR="${CMAKE_INSTALL_FULL_DATADIR}/clips")
set_target_properties(clips_pddl_parser PROPERTIES SOVERSION
                                                ${PROJECT_VERSION_MAJOR})
install(
  TARGETS clips_pddl_parser
  EXPORT ClipsPddlParserTargets
  LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})

install(DIRECTORY include/clips_pddl_parser
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

target_compile_features(clips_pddl_parser PRIVATE cxx_std_17)

install(FILES src/domain.clp DESTINATION ${CMAKE_INSTALL_FULL_DATADIR}/clips)

include(CMakePackageConfigHelpers)
write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/ClipsPddlParserConfigVersion.cmake
  VERSION ${PROJECT_VERSION}
  COMPATIBILITY SameMajorVersion)

install(
  EXPORT ClipsPddlParserTargets
  FILE ClipsPddlParserTargets.cmake
  NAMESPACE ClipsPddlParser::
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/ClipsPddlParser)

install(FILES cmake/ClipsPddlParserConfig.cmake
              ${CMAKE_CURRENT_BINARY_DIR}/ClipsPddlParserConfigVersion.cmake
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/ClipsPddlParser)

set(PKG_CONFIG_REQUIRES "pddl_parser spdlog clipsmm-1.0")

configure_file(clips_pddl_parser.pc.in
               ${CMAKE_CURRENT_BINARY_DIR}/clips_pddl_parser.pc @ONLY)

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/clips_pddl_parser.pc
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/pkgconfig)
