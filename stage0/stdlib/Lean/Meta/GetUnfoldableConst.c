// Lean compiler output
// Module: Lean.Meta.GetUnfoldableConst
// Imports: public import Lean.Meta.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_recordUnfoldAxiom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_getReducibilityStatusCore(v_env_5_, v_declName_1_);
v___x_7_ = lean_box(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_13_, v___y_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___boxed(lean_object* v_declName_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(v_declName_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(lean_object* v_declName_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_43_; 
v___x_27_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_23_, v___y_25_);
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; 
v___x_32_ = lean_unbox(v_a_28_);
lean_dec(v_a_28_);
if (v___x_32_ == 2)
{
uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_33_ = 1;
v___x_34_ = lean_box(v___x_33_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_34_);
v___x_36_ = v___x_30_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
else
{
uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_38_ = 0;
v___x_39_ = lean_box(v___x_38_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_39_);
v___x_41_ = v___x_30_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0___boxed(lean_object* v_declName_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v_declName_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault(lean_object* v_cfg_49_, lean_object* v_info_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
uint8_t v_transparency_54_; 
v_transparency_54_ = lean_ctor_get_uint8(v_cfg_49_, 9);
switch(v_transparency_54_)
{
case 4:
{
uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = 0;
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
case 0:
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = 1;
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
case 1:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = l_Lean_ConstantInfo_name(v_info_50_);
v___x_62_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v___x_61_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_73_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_73_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint8_t v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_67_ = lean_unbox(v_a_63_);
lean_dec(v_a_63_);
v___x_68_ = lean_bool_not(v___x_67_);
v___x_69_ = lean_box(v___x_68_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_69_);
v___x_71_ = v___x_65_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
return v___x_62_;
}
}
default: 
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_114_; 
v___x_74_ = l_Lean_ConstantInfo_name(v_info_50_);
v___x_75_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v___x_74_, v_a_52_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_114_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_114_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_114_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; uint8_t v___x_81_; uint8_t v___x_82_; uint8_t v___x_83_; uint8_t v___y_85_; uint8_t v___y_95_; 
v___x_80_ = 0;
v___x_81_ = lean_unbox(v_a_76_);
v___x_82_ = l_Lean_instBEqReducibilityStatus_beq(v___x_81_, v___x_80_);
v___x_83_ = 1;
if (v___x_82_ == 0)
{
uint8_t v___x_103_; uint8_t v___x_104_; uint8_t v___x_105_; 
v___x_103_ = 4;
v___x_104_ = lean_unbox(v_a_76_);
v___x_105_ = l_Lean_instBEqReducibilityStatus_beq(v___x_104_, v___x_103_);
if (v___x_105_ == 0)
{
v___y_95_ = v___x_105_;
goto v___jp_94_;
}
else
{
uint8_t v___x_106_; uint8_t v___x_107_; 
v___x_106_ = 3;
v___x_107_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_54_, v___x_106_);
if (v___x_107_ == 0)
{
uint8_t v___x_108_; uint8_t v___x_109_; 
v___x_108_ = 5;
v___x_109_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_54_, v___x_108_);
v___y_95_ = v___x_109_;
goto v___jp_94_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_del_object(v___x_78_);
lean_dec(v_a_76_);
v___x_110_ = lean_box(v___x_83_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_del_object(v___x_78_);
lean_dec(v_a_76_);
v___x_112_ = lean_box(v___x_83_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
v___jp_84_:
{
if (v___y_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_box(v___y_85_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_86_);
v___x_88_ = v___x_78_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_box(v___x_83_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_90_);
v___x_92_ = v___x_78_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
v___jp_94_:
{
if (v___y_95_ == 0)
{
uint8_t v___x_96_; uint8_t v___x_97_; uint8_t v___x_98_; 
v___x_96_ = 3;
v___x_97_ = lean_unbox(v_a_76_);
lean_dec(v_a_76_);
v___x_98_ = l_Lean_instBEqReducibilityStatus_beq(v___x_97_, v___x_96_);
if (v___x_98_ == 0)
{
v___y_85_ = v___x_98_;
goto v___jp_84_;
}
else
{
uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 5;
v___x_100_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_54_, v___x_99_);
v___y_85_ = v___x_100_;
goto v___jp_84_;
}
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_del_object(v___x_78_);
lean_dec(v_a_76_);
v___x_101_ = lean_box(v___x_83_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault___boxed(lean_object* v_cfg_115_, lean_object* v_info_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_canUnfoldDefault(v_cfg_115_, v_info_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_info_116_);
lean_dec_ref(v_cfg_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg(lean_object* v_info_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_canUnfold_x3f_126_; lean_object* v___x_127_; 
v_canUnfold_x3f_126_ = lean_ctor_get(v_a_122_, 6);
v___x_127_ = l_Lean_Meta_Context_config(v_a_122_);
if (lean_obj_tag(v_canUnfold_x3f_126_) == 1)
{
lean_object* v_val_128_; lean_object* v___x_129_; 
v_val_128_ = lean_ctor_get(v_canUnfold_x3f_126_, 0);
lean_inc(v_val_128_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_129_ = lean_apply_5(v_val_128_, v___x_127_, v_info_121_, v_a_123_, v_a_124_, lean_box(0));
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_canUnfoldDefault(v___x_127_, v_info_121_, v_a_123_, v_a_124_);
lean_dec_ref(v_info_121_);
lean_dec_ref(v___x_127_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg___boxed(lean_object* v_info_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_canUnfold___redArg(v_info_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec_ref(v_a_132_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object* v_info_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_canUnfold___redArg(v_info_137_, v_a_138_, v_a_140_, v_a_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object* v_info_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_canUnfold(v_info_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; lean_object* v_env_158_; lean_object* v___x_159_; lean_object* v_mctx_160_; lean_object* v_lctx_161_; lean_object* v_options_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_157_ = lean_st_ref_get(v___y_155_);
v_env_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref(v_env_158_);
lean_dec(v___x_157_);
v___x_159_ = lean_st_ref_get(v___y_153_);
v_mctx_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_mctx_160_);
lean_dec(v___x_159_);
v_lctx_161_ = lean_ctor_get(v___y_152_, 2);
v_options_162_ = lean_ctor_get(v___y_154_, 2);
lean_inc_ref(v_options_162_);
lean_inc_ref(v_lctx_161_);
v___x_163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_163_, 0, v_env_158_);
lean_ctor_set(v___x_163_, 1, v_mctx_160_);
lean_ctor_set(v___x_163_, 2, v_lctx_161_);
lean_ctor_set(v___x_163_, 3, v_options_162_);
v___x_164_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_msgData_151_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_ref_179_; lean_object* v___x_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
v_ref_179_ = lean_ctor_get(v___y_176_, 5);
v___x_180_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_189_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_inc(v_ref_179_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_ref_179_);
lean_ctor_set(v___x_185_, 1, v_a_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 1);
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_fileName_204_; lean_object* v_fileMap_205_; lean_object* v_options_206_; lean_object* v_currRecDepth_207_; lean_object* v_maxRecDepth_208_; lean_object* v_ref_209_; lean_object* v_currNamespace_210_; lean_object* v_openDecls_211_; lean_object* v_initHeartbeats_212_; lean_object* v_maxHeartbeats_213_; lean_object* v_quotContext_214_; lean_object* v_currMacroScope_215_; uint8_t v_diag_216_; lean_object* v_cancelTk_x3f_217_; uint8_t v_suppressElabErrors_218_; lean_object* v_inheritedTraceOptions_219_; lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_fileName_204_ = lean_ctor_get(v___y_201_, 0);
v_fileMap_205_ = lean_ctor_get(v___y_201_, 1);
v_options_206_ = lean_ctor_get(v___y_201_, 2);
v_currRecDepth_207_ = lean_ctor_get(v___y_201_, 3);
v_maxRecDepth_208_ = lean_ctor_get(v___y_201_, 4);
v_ref_209_ = lean_ctor_get(v___y_201_, 5);
v_currNamespace_210_ = lean_ctor_get(v___y_201_, 6);
v_openDecls_211_ = lean_ctor_get(v___y_201_, 7);
v_initHeartbeats_212_ = lean_ctor_get(v___y_201_, 8);
v_maxHeartbeats_213_ = lean_ctor_get(v___y_201_, 9);
v_quotContext_214_ = lean_ctor_get(v___y_201_, 10);
v_currMacroScope_215_ = lean_ctor_get(v___y_201_, 11);
v_diag_216_ = lean_ctor_get_uint8(v___y_201_, sizeof(void*)*14);
v_cancelTk_x3f_217_ = lean_ctor_get(v___y_201_, 12);
v_suppressElabErrors_218_ = lean_ctor_get_uint8(v___y_201_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_219_ = lean_ctor_get(v___y_201_, 13);
v_ref_220_ = l_Lean_replaceRef(v_ref_197_, v_ref_209_);
lean_inc_ref(v_inheritedTraceOptions_219_);
lean_inc(v_cancelTk_x3f_217_);
lean_inc(v_currMacroScope_215_);
lean_inc(v_quotContext_214_);
lean_inc(v_maxHeartbeats_213_);
lean_inc(v_initHeartbeats_212_);
lean_inc(v_openDecls_211_);
lean_inc(v_currNamespace_210_);
lean_inc(v_maxRecDepth_208_);
lean_inc(v_currRecDepth_207_);
lean_inc_ref(v_options_206_);
lean_inc_ref(v_fileMap_205_);
lean_inc_ref(v_fileName_204_);
v___x_221_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_221_, 0, v_fileName_204_);
lean_ctor_set(v___x_221_, 1, v_fileMap_205_);
lean_ctor_set(v___x_221_, 2, v_options_206_);
lean_ctor_set(v___x_221_, 3, v_currRecDepth_207_);
lean_ctor_set(v___x_221_, 4, v_maxRecDepth_208_);
lean_ctor_set(v___x_221_, 5, v_ref_220_);
lean_ctor_set(v___x_221_, 6, v_currNamespace_210_);
lean_ctor_set(v___x_221_, 7, v_openDecls_211_);
lean_ctor_set(v___x_221_, 8, v_initHeartbeats_212_);
lean_ctor_set(v___x_221_, 9, v_maxHeartbeats_213_);
lean_ctor_set(v___x_221_, 10, v_quotContext_214_);
lean_ctor_set(v___x_221_, 11, v_currMacroScope_215_);
lean_ctor_set(v___x_221_, 12, v_cancelTk_x3f_217_);
lean_ctor_set(v___x_221_, 13, v_inheritedTraceOptions_219_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*14, v_diag_216_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*14 + 1, v_suppressElabErrors_218_);
v___x_222_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_198_, v___y_199_, v___y_200_, v___x_221_, v___y_202_);
lean_dec_ref_known(v___x_221_, 14);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_223_, v_msg_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_ref_223_);
return v_res_230_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_ctor_set(v___x_236_, 3, v___x_235_);
lean_ctor_set(v___x_236_, 4, v___x_234_);
lean_ctor_set(v___x_236_, 5, v___x_234_);
lean_ctor_set(v___x_236_, 6, v___x_234_);
lean_ctor_set(v___x_236_, 7, v___x_234_);
lean_ctor_set(v___x_236_, 8, v___x_234_);
lean_ctor_set(v___x_236_, 9, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(32u);
v___x_238_ = lean_mk_empty_array_with_capacity(v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_240_ = ((size_t)5ULL);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_unsigned_to_nat(32u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_245_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_241_);
lean_ctor_set(v___x_245_, 3, v___x_241_);
lean_ctor_set_usize(v___x_245_, 4, v___x_240_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_box(1);
v___x_247_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_246_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8));
v___x_255_ = l_Lean_stringToMessageData(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_271_, lean_object* v_declHint_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; lean_object* v_env_276_; uint8_t v___y_278_; uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_275_ = lean_st_ref_get(v___y_273_);
v_env_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc_ref(v_env_276_);
lean_dec(v___x_275_);
v___x_334_ = l_Lean_Name_isAnonymous(v_declHint_272_);
v___x_335_ = lean_bool_not(v___x_334_);
if (v___x_335_ == 0)
{
v___y_278_ = v___x_335_;
goto v___jp_277_;
}
else
{
uint8_t v_isExporting_336_; 
v_isExporting_336_ = lean_ctor_get_uint8(v_env_276_, sizeof(void*)*8);
v___y_278_ = v_isExporting_336_;
goto v___jp_277_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec_ref(v_env_276_);
lean_dec(v_declHint_272_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_msg_271_);
return v___x_279_;
}
else
{
uint8_t v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = 0;
lean_inc_ref(v_env_276_);
v___x_281_ = l_Lean_Environment_setExporting(v_env_276_, v___x_280_);
lean_inc(v_declHint_272_);
lean_inc_ref(v___x_281_);
v___x_282_ = l_Lean_Environment_contains(v___x_281_, v_declHint_272_, v___y_278_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
lean_dec_ref(v___x_281_);
lean_dec_ref(v_env_276_);
lean_dec(v_declHint_272_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_msg_271_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_c_289_; lean_object* v___x_290_; 
v___x_284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_286_ = l_Lean_Options_empty;
v___x_287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_287_, 0, v___x_281_);
lean_ctor_set(v___x_287_, 1, v___x_284_);
lean_ctor_set(v___x_287_, 2, v___x_285_);
lean_ctor_set(v___x_287_, 3, v___x_286_);
lean_inc(v_declHint_272_);
v___x_288_ = l_Lean_MessageData_ofConstName(v_declHint_272_, v___x_280_);
v_c_289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_289_, 0, v___x_287_);
lean_ctor_set(v_c_289_, 1, v___x_288_);
v___x_290_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_276_, v_declHint_272_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref(v_env_276_);
lean_dec(v_declHint_272_);
v___x_291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_c_289_);
v___x_293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_MessageData_note(v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v_msg_271_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_333_; 
v_val_298_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_333_ == 0)
{
v___x_300_ = v___x_290_;
v_isShared_301_ = v_isSharedCheck_333_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v___x_290_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_333_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_mod_305_; uint8_t v___x_306_; 
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_Environment_header(v_env_276_);
lean_dec_ref(v_env_276_);
v___x_304_ = l_Lean_EnvironmentHeader_moduleNames(v___x_303_);
v_mod_305_ = lean_array_get(v___x_302_, v___x_304_, v_val_298_);
lean_dec(v_val_298_);
lean_dec_ref(v___x_304_);
v___x_306_ = l_Lean_isPrivateName(v_declHint_272_);
lean_dec(v_declHint_272_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_307_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_c_289_);
v___x_309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = l_Lean_MessageData_ofName(v_mod_305_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_MessageData_note(v___x_314_);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v_msg_271_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 0);
lean_ctor_set(v___x_300_, 0, v___x_316_);
v___x_318_ = v___x_300_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_320_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_c_289_);
v___x_322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17);
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_MessageData_ofName(v_mod_305_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_MessageData_note(v___x_327_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v_msg_271_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 0);
lean_ctor_set(v___x_300_, 0, v___x_329_);
v___x_331_ = v___x_300_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_337_, lean_object* v_declHint_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_337_, v_declHint_338_, v___y_339_);
lean_dec(v___y_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(lean_object* v_msg_342_, lean_object* v_declHint_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_359_; 
v___x_349_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_342_, v_declHint_343_, v___y_347_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_359_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_354_ = l_Lean_unknownIdentifierMessageTag;
v___x_355_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_355_);
v___x_357_ = v___x_352_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_360_, lean_object* v_declHint_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_360_, v_declHint_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(lean_object* v_ref_368_, lean_object* v_msg_369_, lean_object* v_declHint_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v_a_377_; lean_object* v___x_378_; 
v___x_376_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_369_, v_declHint_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_376_);
v___x_378_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_368_, v_a_377_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_ref_379_, lean_object* v_msg_380_, lean_object* v_declHint_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_379_, v_msg_380_, v_declHint_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v_ref_379_);
return v_res_387_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2));
v___x_393_ = l_Lean_stringToMessageData(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(lean_object* v_ref_394_, lean_object* v_constName_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_401_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1);
v___x_402_ = 0;
lean_inc(v_constName_395_);
v___x_403_ = l_Lean_MessageData_ofConstName(v_constName_395_, v___x_402_);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_401_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_394_, v___x_406_, v_constName_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___boxed(lean_object* v_ref_408_, lean_object* v_constName_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_408_, v_constName_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v_ref_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object* v_constName_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_env_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v___x_422_ = lean_st_ref_get(v_a_420_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_422_);
v___x_424_ = 0;
lean_inc(v_constName_416_);
v___x_425_ = l_Lean_Environment_findAsync_x3f(v_env_423_, v_constName_416_, v___x_424_);
if (lean_obj_tag(v___x_425_) == 1)
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_constName_416_);
v_val_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_461_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_461_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_461_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v_kind_430_; 
v_kind_430_ = lean_ctor_get_uint8(v_val_426_, sizeof(void*)*3);
switch(v_kind_430_)
{
case 1:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_del_object(v___x_428_);
lean_dec(v_val_426_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
case 0:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_426_);
lean_inc_ref(v___x_433_);
v___x_434_ = l_Lean_Meta_canUnfold___redArg(v___x_433_, v_a_417_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_450_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_450_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_450_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_450_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v___x_433_);
lean_del_object(v___x_428_);
v___x_440_ = lean_box(0);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_440_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_445_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_433_);
v___x_445_ = v___x_428_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_433_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_445_);
v___x_447_ = v___x_437_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___x_433_);
lean_del_object(v___x_428_);
v_a_451_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_434_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_434_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
default: 
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_del_object(v___x_428_);
lean_dec(v_val_426_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
}
else
{
lean_object* v_ref_462_; lean_object* v___x_463_; 
lean_dec(v___x_425_);
v_ref_462_ = lean_ctor_get(v_a_419_, 5);
v___x_463_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_462_, v_constName_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object* v_constName_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Meta_getUnfoldableConst_x3f(v_constName_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(lean_object* v_00_u03b1_471_, lean_object* v_ref_472_, lean_object* v_constName_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_472_, v_constName_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___boxed(lean_object* v_00_u03b1_480_, lean_object* v_ref_481_, lean_object* v_constName_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(v_00_u03b1_480_, v_ref_481_, v_constName_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v_ref_481_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(lean_object* v_00_u03b1_489_, lean_object* v_ref_490_, lean_object* v_msg_491_, lean_object* v_declHint_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_490_, v_msg_491_, v_declHint_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_499_, lean_object* v_ref_500_, lean_object* v_msg_501_, lean_object* v_declHint_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(v_00_u03b1_499_, v_ref_500_, v_msg_501_, v_declHint_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v_ref_500_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_msg_509_, lean_object* v_declHint_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_509_, v_declHint_510_, v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msg_517_, lean_object* v_declHint_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(v_msg_517_, v_declHint_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_525_, lean_object* v_ref_526_, lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_526_, v_msg_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_534_, lean_object* v_ref_535_, lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(v_00_u03b1_534_, v_ref_535_, v_msg_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v_ref_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_543_, lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_551_, v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object* v_constName_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_568_; lean_object* v_env_569_; uint8_t v___x_570_; lean_object* v___x_571_; 
v___x_568_ = lean_st_ref_get(v_a_563_);
v_env_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_ref(v_env_569_);
lean_dec(v___x_568_);
v___x_570_ = 0;
lean_inc(v_constName_559_);
v___x_571_ = l_Lean_Environment_find_x3f(v_env_569_, v_constName_559_, v___x_570_);
if (lean_obj_tag(v___x_571_) == 1)
{
lean_object* v_val_572_; 
v_val_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_val_572_);
switch(lean_obj_tag(v_val_572_))
{
case 2:
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref_known(v___x_571_, 1);
lean_dec(v_constName_559_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_val_572_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_val_572_, 0);
lean_dec(v_unused_581_);
v___x_574_ = v_val_572_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_dec(v_val_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 0);
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
case 1:
{
lean_object* v___x_582_; 
lean_dec(v_constName_559_);
v___x_582_ = l_Lean_Meta_canUnfold___redArg(v_val_572_, v_a_560_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_595_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_595_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_595_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_595_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
uint8_t v___x_587_; 
v___x_587_ = lean_unbox(v_a_583_);
lean_dec(v_a_583_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_588_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_593_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_571_);
v___x_593_ = v___x_585_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_571_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref_known(v___x_571_, 1);
v_a_596_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_582_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_582_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
case 0:
{
lean_object* v___x_604_; 
lean_dec_ref_known(v_val_572_, 1);
lean_dec_ref_known(v___x_571_, 1);
v___x_604_ = l_Lean_Meta_recordUnfoldAxiom___redArg(v_constName_559_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_613_);
v___x_606_ = v___x_604_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_dec(v___x_604_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_604_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
default: 
{
lean_dec(v_val_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_dec(v_constName_559_);
goto v___jp_565_;
}
}
}
else
{
lean_dec(v___x_571_);
lean_dec(v_constName_559_);
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object* v_constName_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_getUnfoldableConstNoEx_x3f(v_constName_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
return v_res_628_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_GetUnfoldableConst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_GetUnfoldableConst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_GetUnfoldableConst(builtin);
}
#ifdef __cplusplus
}
#endif
