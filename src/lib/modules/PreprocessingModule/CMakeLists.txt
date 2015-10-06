set(SMTRAT_Preprocessing_Settings "1" CACHE STRING "Number of setting used for PreprocessingModule")

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/PreprocessingModule/PreprocessingModule.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/PreprocessingModule/PreprocessingModule.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/PreprocessingModule/PreprocessingModuleInstantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/PreprocessingModule/PreprocessingModuleInstantiation.h )

BeginDefineModule()
ModuleMainHeader(PreprocessingModule/PreprocessingModule.h)
ModuleName(PreprocessingModule)
ModuleClass(PreprocessingModule<PreprocessingSettings${SMTRAT_Preprocessing_Settings}>)
ModuleVersion(0 0 1)
#ModuleSettingsClass(PreprocessingSettings)
#ModuleSettingsName(standard)
EndDefineModule()
