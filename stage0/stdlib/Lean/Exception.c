// Lean compiler output
// Module: Lean.Exception
// Imports: public import Lean.InternalExceptionId public import Lean.ErrorExplanation
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_kindOfErrorName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_toString(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_error_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_internal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_internal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_getRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_getRef___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedException___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedException___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedException;
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_unknownIdentifierMessageTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_unknownIdentifierMessageTag___closed__0 = (const lean_object*)&l_Lean_unknownIdentifierMessageTag___closed__0_value;
static const lean_string_object l_Lean_unknownIdentifierMessageTag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unknownIdentifier"};
static const lean_object* l_Lean_unknownIdentifierMessageTag___closed__1 = (const lean_object*)&l_Lean_unknownIdentifierMessageTag___closed__1_value;
static const lean_ctor_object l_Lean_unknownIdentifierMessageTag___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unknownIdentifierMessageTag___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 31, 155, 49, 49, 182, 172, 127)}};
static const lean_ctor_object l_Lean_unknownIdentifierMessageTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unknownIdentifierMessageTag___closed__2_value_aux_0),((lean_object*)&l_Lean_unknownIdentifierMessageTag___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 52, 199, 197, 93, 108, 22, 179)}};
static const lean_object* l_Lean_unknownIdentifierMessageTag___closed__2 = (const lean_object*)&l_Lean_unknownIdentifierMessageTag___closed__2_value;
static lean_once_cell_t l_Lean_unknownIdentifierMessageTag___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_unknownIdentifierMessageTag___closed__3;
LEAN_EXPORT lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "interrupt"};
static const lean_object* l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 100, 242, 233, 23, 237, 26, 183)}};
static const lean_object* l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_interruptExceptionId;
static lean_once_cell_t l_Lean_throwInterruptException___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_termThrowError_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_termThrowError_____00__closed__0 = (const lean_object*)&l_Lean_termThrowError_____00__closed__0_value;
static const lean_string_object l_Lean_termThrowError_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "termThrowError__"};
static const lean_object* l_Lean_termThrowError_____00__closed__1 = (const lean_object*)&l_Lean_termThrowError_____00__closed__1_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termThrowError_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__2_value_aux_0),((lean_object*)&l_Lean_termThrowError_____00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 45, 105, 121, 242, 5, 105, 46)}};
static const lean_object* l_Lean_termThrowError_____00__closed__2 = (const lean_object*)&l_Lean_termThrowError_____00__closed__2_value;
static const lean_string_object l_Lean_termThrowError_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termThrowError_____00__closed__3 = (const lean_object*)&l_Lean_termThrowError_____00__closed__3_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termThrowError_____00__closed__4 = (const lean_object*)&l_Lean_termThrowError_____00__closed__4_value;
static const lean_string_object l_Lean_termThrowError_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "throwError "};
static const lean_object* l_Lean_termThrowError_____00__closed__5 = (const lean_object*)&l_Lean_termThrowError_____00__closed__5_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__5_value)}};
static const lean_object* l_Lean_termThrowError_____00__closed__6 = (const lean_object*)&l_Lean_termThrowError_____00__closed__6_value;
static const lean_string_object l_Lean_termThrowError_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_termThrowError_____00__closed__7 = (const lean_object*)&l_Lean_termThrowError_____00__closed__7_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_termThrowError_____00__closed__8 = (const lean_object*)&l_Lean_termThrowError_____00__closed__8_value;
static const lean_string_object l_Lean_termThrowError_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_termThrowError_____00__closed__9 = (const lean_object*)&l_Lean_termThrowError_____00__closed__9_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_termThrowError_____00__closed__10 = (const lean_object*)&l_Lean_termThrowError_____00__closed__10_value;
static const lean_string_object l_Lean_termThrowError_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_termThrowError_____00__closed__11 = (const lean_object*)&l_Lean_termThrowError_____00__closed__11_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__11_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_termThrowError_____00__closed__12 = (const lean_object*)&l_Lean_termThrowError_____00__closed__12_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_termThrowError_____00__closed__13 = (const lean_object*)&l_Lean_termThrowError_____00__closed__13_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__10_value),((lean_object*)&l_Lean_termThrowError_____00__closed__13_value)}};
static const lean_object* l_Lean_termThrowError_____00__closed__14 = (const lean_object*)&l_Lean_termThrowError_____00__closed__14_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__8_value),((lean_object*)&l_Lean_termThrowError_____00__closed__14_value),((lean_object*)&l_Lean_termThrowError_____00__closed__13_value)}};
static const lean_object* l_Lean_termThrowError_____00__closed__15 = (const lean_object*)&l_Lean_termThrowError_____00__closed__15_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__4_value),((lean_object*)&l_Lean_termThrowError_____00__closed__6_value),((lean_object*)&l_Lean_termThrowError_____00__closed__15_value)}};
static const lean_object* l_Lean_termThrowError_____00__closed__16 = (const lean_object*)&l_Lean_termThrowError_____00__closed__16_value;
static const lean_ctor_object l_Lean_termThrowError_____00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__16_value)}};
static const lean_object* l_Lean_termThrowError_____00__closed__17 = (const lean_object*)&l_Lean_termThrowError_____00__closed__17_value;
LEAN_EXPORT const lean_object* l_Lean_termThrowError____ = (const lean_object*)&l_Lean_termThrowError_____00__closed__17_value;
static const lean_string_object l_Lean_termThrowErrorAt_________00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "termThrowErrorAt____"};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__0 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__0_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__1_value_aux_0),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 135, 54, 14, 35, 246, 144, 68)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__1 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__1_value;
static const lean_string_object l_Lean_termThrowErrorAt_________00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "throwErrorAt "};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__2 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__2_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__2_value)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__3 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__3_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__12_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__4 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__4_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__4_value),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__3_value),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__4_value)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__5 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__5_value;
static const lean_string_object l_Lean_termThrowErrorAt_________00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__6 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__6_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__7 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__7_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__7_value)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__8 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__8_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__4_value),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__5_value),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__8_value)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__9 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__9_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termThrowError_____00__closed__4_value),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__9_value),((lean_object*)&l_Lean_termThrowError_____00__closed__15_value)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__10 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__10_value;
static const lean_ctor_object l_Lean_termThrowErrorAt_________00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termThrowErrorAt_________00__closed__10_value)}};
static const lean_object* l_Lean_termThrowErrorAt_________00__closed__11 = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_termThrowErrorAt________ = (const lean_object*)&l_Lean_termThrowErrorAt_________00__closed__11_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.throwError"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6_value;
static lean_once_cell_t l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "throwError"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(205, 114, 235, 161, 61, 182, 120, 70)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value;
static lean_once_cell_t l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.throwErrorAt"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0_value;
static lean_once_cell_t l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "throwErrorAt"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 66, 91, 242, 19, 251, 76, 72)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Exception_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_ref_7_; lean_object* v_msg_8_; lean_object* v___x_9_; 
v_ref_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ref_7_);
v_msg_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_msg_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_ref_7_, v_msg_8_);
return v___x_9_;
}
else
{
lean_object* v_id_10_; lean_object* v_extra_11_; lean_object* v___x_12_; 
v_id_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_id_10_);
v_extra_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_extra_11_);
lean_dec_ref_known(v_t_5_, 2);
v___x_12_ = lean_apply_2(v_k_6_, v_id_10_, v_extra_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Exception_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Exception_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_error_elim___redArg(lean_object* v_t_25_, lean_object* v_error_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Exception_ctorElim___redArg(v_t_25_, v_error_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_error_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_error_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Exception_ctorElim___redArg(v_t_29_, v_error_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_internal_elim___redArg(lean_object* v_t_33_, lean_object* v_internal_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Exception_ctorElim___redArg(v_t_33_, v_internal_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_internal_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_internal_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Exception_ctorElim___redArg(v_t_37_, v_internal_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_toMessageData(lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_object* v_msg_42_; 
v_msg_42_ = lean_ctor_get(v_x_41_, 1);
lean_inc_ref(v_msg_42_);
lean_dec_ref_known(v_x_41_, 2);
return v_msg_42_;
}
else
{
lean_object* v_id_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_id_43_ = lean_ctor_get(v_x_41_, 0);
lean_inc(v_id_43_);
lean_dec_ref_known(v_x_41_, 2);
v___x_44_ = l_Lean_InternalExceptionId_toString(v_id_43_);
v___x_45_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
v___x_46_ = l_Lean_MessageData_ofFormat(v___x_45_);
return v___x_46_;
}
}
}
uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v_msg_48_; uint8_t v___x_49_; 
v_msg_48_ = lean_ctor_get(v_x_47_, 1);
lean_inc_ref(v_msg_48_);
lean_dec_ref_known(v_x_47_, 2);
v___x_49_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_48_);
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
lean_dec_ref(v_x_47_);
v___x_50_ = 0;
return v___x_50_;
}
}
}
LEAN_EXPORT void l_Lean_Exception_hasSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_47_ = stack[0].m_obj;
uint8_t v_res_51_;
v_res_51_ = l_Lean_Exception_hasSyntheticSorry(v_x_47_);
stack->m_num = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lean_Exception_hasSyntheticSorry(v_x_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_getRef(lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v_ref_56_; 
v_ref_56_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_ref_56_);
return v_ref_56_;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_getRef___boxed(lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Exception_getRef(v_x_58_);
lean_dec_ref(v_x_58_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_instInhabitedException___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = l_Lean_instInhabitedMessageData_default;
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_instInhabitedException(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Lean_instInhabitedException___closed__0, &l_Lean_instInhabitedException___closed__0_once, _init_l_Lean_instInhabitedException___closed__0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(lean_object* v_ref_64_, lean_object* v_toPure_65_, lean_object* v_msg_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_ref_64_);
lean_ctor_set(v___x_67_, 1, v_msg_66_);
v___x_68_ = lean_apply_2(v_toPure_65_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(lean_object* v_toPure_69_, lean_object* v_inst_70_, lean_object* v_toBind_71_, lean_object* v_ref_72_, lean_object* v_msg_73_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___f_74_ = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_74_, 0, v_ref_72_);
lean_closure_set(v___f_74_, 1, v_toPure_69_);
v___x_75_ = lean_apply_1(v_inst_70_, v_msg_73_);
v___x_76_ = lean_apply_4(v_toBind_71_, lean_box(0), lean_box(0), v___x_75_, v___f_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object* v_inst_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v_toApplicative_79_; lean_object* v_toBind_80_; lean_object* v_toPure_81_; lean_object* v___f_82_; 
v_toApplicative_79_ = lean_ctor_get(v_inst_78_, 0);
lean_inc_ref(v_toApplicative_79_);
v_toBind_80_ = lean_ctor_get(v_inst_78_, 1);
lean_inc(v_toBind_80_);
lean_dec_ref(v_inst_78_);
v_toPure_81_ = lean_ctor_get(v_toApplicative_79_, 1);
lean_inc(v_toPure_81_);
lean_dec_ref(v_toApplicative_79_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_82_, 0, v_toPure_81_);
lean_closure_set(v___f_82_, 1, v_inst_77_);
lean_closure_set(v___f_82_, 2, v_toBind_80_);
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_object* v_m_83_, lean_object* v_inst_84_, lean_object* v_inst_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v_inst_84_, v_inst_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0(lean_object* v_toMonadExceptOf_87_, lean_object* v_____x_88_){
_start:
{
lean_object* v_fst_89_; lean_object* v_snd_90_; lean_object* v_throw_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_99_; 
v_fst_89_ = lean_ctor_get(v_____x_88_, 0);
v_snd_90_ = lean_ctor_get(v_____x_88_, 1);
v_throw_91_ = lean_ctor_get(v_toMonadExceptOf_87_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_toMonadExceptOf_87_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v_toMonadExceptOf_87_, 1);
lean_dec(v_unused_100_);
v___x_93_ = v_toMonadExceptOf_87_;
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_throw_91_);
lean_dec(v_toMonadExceptOf_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
lean_inc(v_snd_90_);
lean_inc(v_fst_89_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v_snd_90_);
lean_ctor_set(v___x_93_, 0, v_fst_89_);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_fst_89_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_snd_90_);
v___x_96_ = v_reuseFailAlloc_98_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_2(v_throw_91_, lean_box(0), v___x_96_);
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0___boxed(lean_object* v_toMonadExceptOf_101_, lean_object* v_____x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_throwError___redArg___lam__0(v_toMonadExceptOf_101_, v_____x_102_);
lean_dec_ref(v_____x_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__1(lean_object* v_toAddErrorMessageContext_104_, lean_object* v_msg_105_, lean_object* v_toBind_106_, lean_object* v___f_107_, lean_object* v_ref_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_apply_2(v_toAddErrorMessageContext_104_, v_ref_108_, v_msg_105_);
v___x_110_ = lean_apply_4(v_toBind_106_, lean_box(0), lean_box(0), v___x_109_, v___f_107_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_msg_113_){
_start:
{
lean_object* v_toMonadRef_114_; lean_object* v_toBind_115_; lean_object* v_toMonadExceptOf_116_; lean_object* v_toAddErrorMessageContext_117_; lean_object* v_getRef_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v_toMonadRef_114_ = lean_ctor_get(v_inst_112_, 1);
lean_inc_ref(v_toMonadRef_114_);
v_toBind_115_ = lean_ctor_get(v_inst_111_, 1);
lean_inc_n(v_toBind_115_, 2);
lean_dec_ref(v_inst_111_);
v_toMonadExceptOf_116_ = lean_ctor_get(v_inst_112_, 0);
lean_inc_ref(v_toMonadExceptOf_116_);
v_toAddErrorMessageContext_117_ = lean_ctor_get(v_inst_112_, 2);
lean_inc(v_toAddErrorMessageContext_117_);
lean_dec_ref(v_inst_112_);
v_getRef_118_ = lean_ctor_get(v_toMonadRef_114_, 0);
lean_inc(v_getRef_118_);
lean_dec_ref(v_toMonadRef_114_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v_toMonadExceptOf_116_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__1), 5, 4);
lean_closure_set(v___f_120_, 0, v_toAddErrorMessageContext_117_);
lean_closure_set(v___f_120_, 1, v_msg_113_);
lean_closure_set(v___f_120_, 2, v_toBind_115_);
lean_closure_set(v___f_120_, 3, v___f_119_);
v___x_121_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v_getRef_118_, v___f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError(lean_object* v_m_122_, lean_object* v_00_u03b1_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_msg_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_throwError___redArg(v_inst_124_, v_inst_125_, v_msg_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_unknownIdentifierMessageTag___closed__2));
v___x_134_ = l_Lean_kindOfErrorName(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_unknownIdentifierMessageTag___closed__3, &l_Lean_unknownIdentifierMessageTag___closed__3_once, _init_l_Lean_unknownIdentifierMessageTag___closed__3);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0(lean_object* v_ref_136_, lean_object* v_withRef_137_, lean_object* v___x_138_, lean_object* v_oldRef_139_){
_start:
{
lean_object* v_ref_140_; lean_object* v___x_141_; 
v_ref_140_ = l_Lean_replaceRef(v_ref_136_, v_oldRef_139_);
v___x_141_ = lean_apply_3(v_withRef_137_, lean_box(0), v_ref_140_, v___x_138_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0___boxed(lean_object* v_ref_142_, lean_object* v_withRef_143_, lean_object* v___x_144_, lean_object* v_oldRef_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_throwErrorAt___redArg___lam__0(v_ref_142_, v_withRef_143_, v___x_144_, v_oldRef_145_);
lean_dec(v_oldRef_145_);
lean_dec(v_ref_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_ref_149_, lean_object* v_msg_150_){
_start:
{
lean_object* v_toMonadRef_151_; lean_object* v_toBind_152_; lean_object* v_getRef_153_; lean_object* v_withRef_154_; lean_object* v___x_155_; lean_object* v___f_156_; lean_object* v___x_157_; 
v_toMonadRef_151_ = lean_ctor_get(v_inst_148_, 1);
v_toBind_152_ = lean_ctor_get(v_inst_147_, 1);
lean_inc(v_toBind_152_);
v_getRef_153_ = lean_ctor_get(v_toMonadRef_151_, 0);
lean_inc(v_getRef_153_);
v_withRef_154_ = lean_ctor_get(v_toMonadRef_151_, 1);
lean_inc(v_withRef_154_);
v___x_155_ = l_Lean_throwError___redArg(v_inst_147_, v_inst_148_, v_msg_150_);
v___f_156_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_156_, 0, v_ref_149_);
lean_closure_set(v___f_156_, 1, v_withRef_154_);
lean_closure_set(v___f_156_, 2, v___x_155_);
v___x_157_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v_getRef_153_, v___f_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt(lean_object* v_m_158_, lean_object* v_00_u03b1_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_ref_162_, lean_object* v_msg_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_throwErrorAt___redArg(v_inst_160_, v_inst_161_, v_ref_162_, v_msg_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg___lam__1(lean_object* v_msg_165_, lean_object* v_name_166_, lean_object* v_toAddErrorMessageContext_167_, lean_object* v_toBind_168_, lean_object* v___f_169_, lean_object* v_ref_170_){
_start:
{
lean_object* v_msg_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_msg_171_ = l_Lean_MessageData_tagWithErrorName(v_msg_165_, v_name_166_);
v___x_172_ = lean_apply_2(v_toAddErrorMessageContext_167_, v_ref_170_, v_msg_171_);
v___x_173_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_172_, v___f_169_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg(lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_name_176_, lean_object* v_msg_177_){
_start:
{
lean_object* v_toMonadRef_178_; lean_object* v_toBind_179_; lean_object* v_toMonadExceptOf_180_; lean_object* v_toAddErrorMessageContext_181_; lean_object* v_getRef_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; 
v_toMonadRef_178_ = lean_ctor_get(v_inst_175_, 1);
lean_inc_ref(v_toMonadRef_178_);
v_toBind_179_ = lean_ctor_get(v_inst_174_, 1);
lean_inc_n(v_toBind_179_, 2);
lean_dec_ref(v_inst_174_);
v_toMonadExceptOf_180_ = lean_ctor_get(v_inst_175_, 0);
lean_inc_ref(v_toMonadExceptOf_180_);
v_toAddErrorMessageContext_181_ = lean_ctor_get(v_inst_175_, 2);
lean_inc(v_toAddErrorMessageContext_181_);
lean_dec_ref(v_inst_175_);
v_getRef_182_ = lean_ctor_get(v_toMonadRef_178_, 0);
lean_inc(v_getRef_182_);
lean_dec_ref(v_toMonadRef_178_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_183_, 0, v_toMonadExceptOf_180_);
v___f_184_ = lean_alloc_closure((void*)(l_Lean_throwNamedError___redArg___lam__1), 6, 5);
lean_closure_set(v___f_184_, 0, v_msg_177_);
lean_closure_set(v___f_184_, 1, v_name_176_);
lean_closure_set(v___f_184_, 2, v_toAddErrorMessageContext_181_);
lean_closure_set(v___f_184_, 3, v_toBind_179_);
lean_closure_set(v___f_184_, 4, v___f_183_);
v___x_185_ = lean_apply_4(v_toBind_179_, lean_box(0), lean_box(0), v_getRef_182_, v___f_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError(lean_object* v_m_186_, lean_object* v_00_u03b1_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_name_190_, lean_object* v_msg_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_throwNamedError___redArg(v_inst_188_, v_inst_189_, v_name_190_, v_msg_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt___redArg(lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_ref_195_, lean_object* v_name_196_, lean_object* v_msg_197_){
_start:
{
lean_object* v_toMonadRef_198_; lean_object* v_toBind_199_; lean_object* v_getRef_200_; lean_object* v_withRef_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_204_; 
v_toMonadRef_198_ = lean_ctor_get(v_inst_194_, 1);
v_toBind_199_ = lean_ctor_get(v_inst_193_, 1);
lean_inc(v_toBind_199_);
v_getRef_200_ = lean_ctor_get(v_toMonadRef_198_, 0);
lean_inc(v_getRef_200_);
v_withRef_201_ = lean_ctor_get(v_toMonadRef_198_, 1);
lean_inc(v_withRef_201_);
v___x_202_ = l_Lean_throwNamedError___redArg(v_inst_193_, v_inst_194_, v_name_196_, v_msg_197_);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_203_, 0, v_ref_195_);
lean_closure_set(v___f_203_, 1, v_withRef_201_);
lean_closure_set(v___f_203_, 2, v___x_202_);
v___x_204_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v_getRef_200_, v___f_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt(lean_object* v_m_205_, lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_ref_209_, lean_object* v_name_210_, lean_object* v_msg_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_throwNamedErrorAt___redArg(v_inst_207_, v_inst_208_, v_ref_209_, v_name_210_, v_msg_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_213_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_217_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
lean_ctor_set(v___x_219_, 2, v___x_218_);
lean_ctor_set(v___x_219_, 3, v___x_218_);
lean_ctor_set(v___x_219_, 4, v___x_217_);
lean_ctor_set(v___x_219_, 5, v___x_217_);
lean_ctor_set(v___x_219_, 6, v___x_217_);
lean_ctor_set(v___x_219_, 7, v___x_217_);
lean_ctor_set(v___x_219_, 8, v___x_217_);
lean_ctor_set(v___x_219_, 9, v___x_217_);
lean_ctor_set(v___x_219_, 10, v___x_217_);
lean_ctor_set(v___x_219_, 11, v___x_216_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_unsigned_to_nat(32u);
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_220_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4(void){
_start:
{
size_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_223_ = ((size_t)5ULL);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_unsigned_to_nat(32u);
v___x_226_ = lean_mk_empty_array_with_capacity(v___x_225_);
v___x_227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3);
v___x_228_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_224_);
lean_ctor_set(v___x_228_, 3, v___x_224_);
lean_ctor_set_usize(v___x_228_, 4, v___x_223_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = lean_box(1);
v___x_230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4);
v___x_231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1);
v___x_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_229_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18));
v___x_253_ = l_Lean_stringToMessageData(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__20));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__22));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__24));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__26));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object* v_declHint_266_, lean_object* v_toPure_267_, lean_object* v_msg_268_, lean_object* v___x_269_, lean_object* v_env_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = l_Lean_Name_isAnonymous(v_declHint_266_);
if (v___x_271_ == 0)
{
uint8_t v_isExporting_272_; 
v_isExporting_272_ = lean_ctor_get_uint8(v_env_270_, sizeof(void*)*13);
if (v_isExporting_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v_env_270_);
lean_dec(v_declHint_266_);
v___x_273_ = lean_apply_2(v_toPure_267_, lean_box(0), v_msg_268_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; uint8_t v___x_275_; 
lean_inc_ref(v_env_270_);
v___x_274_ = l_Lean_Environment_setExporting(v_env_270_, v___x_271_);
lean_inc(v_declHint_266_);
lean_inc_ref(v___x_274_);
v___x_275_ = l_Lean_Environment_contains(v___x_274_, v_declHint_266_, v_isExporting_272_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v___x_274_);
lean_dec_ref(v_env_270_);
lean_dec(v_declHint_266_);
v___x_276_ = lean_apply_2(v_toPure_267_, lean_box(0), v_msg_268_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_c_282_; lean_object* v___x_283_; 
v___x_277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2);
v___x_278_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5);
v___x_279_ = l_Lean_Options_empty;
v___x_280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_280_, 0, v___x_274_);
lean_ctor_set(v___x_280_, 1, v___x_277_);
lean_ctor_set(v___x_280_, 2, v___x_278_);
lean_ctor_set(v___x_280_, 3, v___x_279_);
lean_inc(v_declHint_266_);
v___x_281_ = l_Lean_MessageData_ofConstName(v_declHint_266_, v___x_271_);
v_c_282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_282_, 0, v___x_280_);
lean_ctor_set(v_c_282_, 1, v___x_281_);
v___x_283_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_270_, v_declHint_266_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec_ref(v_env_270_);
lean_dec(v_declHint_266_);
v___x_284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v_c_282_);
v___x_286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_MessageData_note(v___x_287_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v_msg_268_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; lean_object* v_modules_293_; lean_object* v_moduleNames_294_; lean_object* v_mod_295_; uint8_t v___y_297_; uint8_t v___x_323_; 
v_val_291_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_283_, 1);
v___x_292_ = l_Lean_Environment_header(v_env_270_);
lean_dec_ref(v_env_270_);
v_modules_293_ = lean_ctor_get(v___x_292_, 3);
lean_inc_ref(v_modules_293_);
v_moduleNames_294_ = lean_ctor_get(v___x_292_, 4);
lean_inc_ref(v_moduleNames_294_);
lean_dec_ref(v___x_292_);
v_mod_295_ = lean_array_get(v___x_269_, v_moduleNames_294_, v_val_291_);
lean_dec_ref(v_moduleNames_294_);
v___x_323_ = l_Lean_isPrivateName(v_declHint_266_);
lean_dec(v_declHint_266_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_get_size(v_modules_293_);
v___x_325_ = lean_nat_dec_lt(v_val_291_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec_ref(v_modules_293_);
lean_dec(v_val_291_);
v___y_297_ = v___x_323_;
goto v___jp_296_;
}
else
{
lean_object* v___x_326_; lean_object* v_toImport_327_; uint8_t v_isExported_328_; 
v___x_326_ = lean_array_fget(v_modules_293_, v_val_291_);
lean_dec(v_val_291_);
lean_dec_ref(v_modules_293_);
v_toImport_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_toImport_327_);
lean_dec(v___x_326_);
v_isExported_328_ = lean_ctor_get_uint8(v_toImport_327_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_327_);
v___y_297_ = v_isExported_328_;
goto v___jp_296_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v_modules_293_);
lean_dec(v_val_291_);
v___x_329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_c_282_);
v___x_331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_MessageData_ofName(v_mod_295_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_MessageData_note(v___x_336_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v_msg_268_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_338_);
return v___x_339_;
}
v___jp_296_:
{
if (v___y_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_c_282_);
v___x_300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Lean_MessageData_ofName(v_mod_295_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_MessageData_note(v___x_305_);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v_msg_268_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_c_282_);
v___x_311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_MessageData_ofName(v_mod_295_);
lean_inc_ref(v___x_313_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_313_);
v___x_318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Lean_MessageData_note(v___x_319_);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v_msg_268_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_321_);
return v___x_322_;
}
}
}
}
}
}
else
{
lean_object* v___x_340_; 
lean_dec_ref(v_env_270_);
lean_dec(v_declHint_266_);
v___x_340_ = lean_apply_2(v_toPure_267_, lean_box(0), v_msg_268_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed(lean_object* v_declHint_341_, lean_object* v_toPure_342_, lean_object* v_msg_343_, lean_object* v___x_344_, lean_object* v_env_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(v_declHint_341_, v_toPure_342_, v_msg_343_, v___x_344_, v_env_345_);
lean_dec(v___x_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_msg_349_, lean_object* v_declHint_350_){
_start:
{
lean_object* v_toApplicative_351_; lean_object* v_toBind_352_; lean_object* v_getEnv_353_; lean_object* v_toPure_354_; lean_object* v___x_355_; lean_object* v___f_356_; lean_object* v___x_357_; 
v_toApplicative_351_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_ref(v_toApplicative_351_);
v_toBind_352_ = lean_ctor_get(v_inst_347_, 1);
lean_inc(v_toBind_352_);
lean_dec_ref(v_inst_347_);
v_getEnv_353_ = lean_ctor_get(v_inst_348_, 0);
lean_inc(v_getEnv_353_);
lean_dec_ref(v_inst_348_);
v_toPure_354_ = lean_ctor_get(v_toApplicative_351_, 1);
lean_inc(v_toPure_354_);
lean_dec_ref(v_toApplicative_351_);
v___x_355_ = lean_box(0);
v___f_356_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_356_, 0, v_declHint_350_);
lean_closure_set(v___f_356_, 1, v_toPure_354_);
lean_closure_set(v___f_356_, 2, v_msg_349_);
lean_closure_set(v___f_356_, 3, v___x_355_);
v___x_357_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v_getEnv_353_, v___f_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore(lean_object* v_m_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_msg_362_, lean_object* v_declHint_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_359_, v_inst_360_, v_msg_362_, v_declHint_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___boxed(lean_object* v_m_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_msg_369_, lean_object* v_declHint_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_mkUnknownIdentifierMessageCore(v_m_365_, v_inst_366_, v_inst_367_, v_inst_368_, v_msg_369_, v_declHint_370_);
lean_dec_ref(v_inst_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(lean_object* v_toPure_372_, lean_object* v_msg_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = l_Lean_unknownIdentifierMessageTag;
v___x_375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_msg_373_);
v___x_376_ = lean_apply_2(v_toPure_372_, lean_box(0), v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg(lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_msg_379_, lean_object* v_declHint_380_){
_start:
{
lean_object* v_toApplicative_381_; lean_object* v_toBind_382_; lean_object* v_toPure_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; 
v_toApplicative_381_ = lean_ctor_get(v_inst_377_, 0);
v_toBind_382_ = lean_ctor_get(v_inst_377_, 1);
lean_inc(v_toBind_382_);
v_toPure_383_ = lean_ctor_get(v_toApplicative_381_, 1);
lean_inc(v_toPure_383_);
v___x_384_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_377_, v_inst_378_, v_msg_379_, v_declHint_380_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_385_, 0, v_toPure_383_);
v___x_386_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_384_, v___f_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object* v_m_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_msg_391_, lean_object* v_declHint_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_388_, v_inst_389_, v_msg_391_, v_declHint_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___boxed(lean_object* v_m_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_msg_398_, lean_object* v_declHint_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_mkUnknownIdentifierMessage(v_m_394_, v_inst_395_, v_inst_396_, v_inst_397_, v_msg_398_, v_declHint_399_);
lean_dec_ref(v_inst_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg___lam__0(lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_ref_403_, lean_object* v_____do__lift_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_throwErrorAt___redArg(v_inst_401_, v_inst_402_, v_ref_403_, v_____do__lift_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_ref_409_, lean_object* v_msg_410_, lean_object* v_declHint_411_){
_start:
{
lean_object* v_toBind_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_toBind_412_ = lean_ctor_get(v_inst_406_, 1);
lean_inc(v_toBind_412_);
lean_inc_ref(v_inst_406_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_throwUnknownIdentifierAt___redArg___lam__0), 4, 3);
lean_closure_set(v___f_413_, 0, v_inst_406_);
lean_closure_set(v___f_413_, 1, v_inst_408_);
lean_closure_set(v___f_413_, 2, v_ref_409_);
v___x_414_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_406_, v_inst_407_, v_msg_410_, v_declHint_411_);
v___x_415_ = lean_apply_4(v_toBind_412_, lean_box(0), lean_box(0), v___x_414_, v___f_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object* v_m_416_, lean_object* v_00_u03b1_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_ref_421_, lean_object* v_msg_422_, lean_object* v_declHint_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_418_, v_inst_419_, v_inst_420_, v_ref_421_, v_msg_422_, v_declHint_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__0));
v___x_427_ = l_Lean_stringToMessageData(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__2));
v___x_430_ = l_Lean_stringToMessageData(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_ref_434_, lean_object* v_constName_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_436_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__1, &l_Lean_throwUnknownConstantAt___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__1);
v___x_437_ = 0;
lean_inc(v_constName_435_);
v___x_438_ = l_Lean_MessageData_ofConstName(v_constName_435_, v___x_437_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_436_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__3, &l_Lean_throwUnknownConstantAt___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__3);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_ref_434_, v___x_441_, v_constName_435_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object* v_m_443_, lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_ref_448_, lean_object* v_constName_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_ref_448_, v_constName_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_constName_454_, lean_object* v_____do__lift_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_451_, v_inst_452_, v_inst_453_, v_____do__lift_455_, v_constName_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_constName_460_){
_start:
{
lean_object* v_toMonadRef_461_; lean_object* v_toBind_462_; lean_object* v_getRef_463_; lean_object* v___f_464_; lean_object* v___x_465_; 
v_toMonadRef_461_ = lean_ctor_get(v_inst_459_, 1);
v_toBind_462_ = lean_ctor_get(v_inst_457_, 1);
lean_inc(v_toBind_462_);
v_getRef_463_ = lean_ctor_get(v_toMonadRef_461_, 0);
lean_inc(v_getRef_463_);
v___f_464_ = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___redArg___lam__0), 5, 4);
lean_closure_set(v___f_464_, 0, v_inst_457_);
lean_closure_set(v___f_464_, 1, v_inst_458_);
lean_closure_set(v___f_464_, 2, v_inst_459_);
lean_closure_set(v___f_464_, 3, v_constName_460_);
v___x_465_ = lean_apply_4(v_toBind_462_, lean_box(0), lean_box(0), v_getRef_463_, v___f_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object* v_m_466_, lean_object* v_00_u03b1_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_constName_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_throwUnknownConstant___redArg(v_inst_468_, v_inst_469_, v_inst_470_, v_constName_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_a_477_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v_x_476_, 1);
v___x_478_ = lean_apply_1(v_inst_475_, v_a_477_);
v___x_479_ = l_Lean_throwError___redArg(v_inst_473_, v_inst_474_, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_toApplicative_480_; lean_object* v_toPure_481_; lean_object* v_a_482_; lean_object* v___x_483_; 
v_toApplicative_480_ = lean_ctor_get(v_inst_473_, 0);
lean_inc_ref(v_toApplicative_480_);
lean_dec_ref(v_inst_475_);
lean_dec_ref(v_inst_474_);
lean_dec_ref(v_inst_473_);
v_toPure_481_ = lean_ctor_get(v_toApplicative_480_, 1);
lean_inc(v_toPure_481_);
lean_dec_ref(v_toApplicative_480_);
v_a_482_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v_x_476_, 1);
v___x_483_ = lean_apply_2(v_toPure_481_, lean_box(0), v_a_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object* v_m_484_, lean_object* v_00_u03b5_485_, lean_object* v_00_u03b1_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_ofExcept___redArg(v_inst_487_, v_inst_488_, v_inst_489_, v_x_490_);
return v___x_491_;
}
}
lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_));
v___x_497_ = l_Lean_registerInternalExceptionId(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT void l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_498_;
v_res_498_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
return v_res_500_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_box(0);
v___x_502_ = l_Lean_interruptExceptionId;
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object* v_inst_504_){
_start:
{
lean_object* v_toMonadExceptOf_505_; lean_object* v_throw_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_toMonadExceptOf_505_ = lean_ctor_get(v_inst_504_, 0);
lean_inc_ref(v_toMonadExceptOf_505_);
lean_dec_ref(v_inst_504_);
v_throw_506_ = lean_ctor_get(v_toMonadExceptOf_505_, 0);
lean_inc(v_throw_506_);
lean_dec_ref(v_toMonadExceptOf_505_);
v___x_507_ = lean_obj_once(&l_Lean_throwInterruptException___redArg___closed__0, &l_Lean_throwInterruptException___redArg___closed__0_once, _init_l_Lean_throwInterruptException___redArg___closed__0);
v___x_508_ = lean_apply_2(v_throw_506_, lean_box(0), v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object* v_m_509_, lean_object* v_00_u03b1_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_throwInterruptException___redArg(v_inst_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object* v_m_515_, lean_object* v_00_u03b1_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_throwInterruptException(v_m_515_, v_00_u03b1_516_, v_inst_517_, v_inst_518_, v_inst_519_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_517_);
return v_res_520_;
}
}
uint8_t l_Lean_Exception_isInterrupt(lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 1)
{
lean_object* v_id_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_id_522_ = lean_ctor_get(v_x_521_, 0);
v___x_523_ = l_Lean_interruptExceptionId;
v___x_524_ = l_Lean_instBEqInternalExceptionId_beq(v_id_522_, v___x_523_);
return v___x_524_;
}
else
{
uint8_t v___x_525_; 
v___x_525_ = 0;
return v___x_525_;
}
}
}
LEAN_EXPORT void l_Lean_Exception_isInterrupt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_521_ = stack[0].m_obj;
uint8_t v_res_526_;
v_res_526_ = l_Lean_Exception_isInterrupt(v_x_521_);
stack->m_num = v_res_526_;
}
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object* v_x_527_){
_start:
{
uint8_t v_res_528_; lean_object* v_r_529_; 
v_res_528_ = l_Lean_Exception_isInterrupt(v_x_527_);
lean_dec_ref(v_x_527_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object* v_ex_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_____do__lift_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_Lean_Kernel_Exception_toMessageData(v_ex_530_, v_____do__lift_533_);
v___x_535_ = l_Lean_throwError___redArg(v_inst_531_, v_inst_532_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object* v_inst_536_, lean_object* v_toBind_537_, lean_object* v___f_538_, lean_object* v_____r_539_){
_start:
{
lean_object* v_getOptions_540_; lean_object* v___x_541_; 
v_getOptions_540_ = lean_ctor_get(v_inst_536_, 0);
lean_inc(v_getOptions_540_);
lean_dec_ref(v_inst_536_);
v___x_541_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v_getOptions_540_, v___f_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__2(lean_object* v___f_542_, lean_object* v_____r_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_apply_1(v___f_542_, v_____r_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_ex_548_){
_start:
{
lean_object* v_toBind_549_; lean_object* v___f_550_; lean_object* v___f_551_; 
v_toBind_549_ = lean_ctor_get(v_inst_545_, 1);
lean_inc_n(v_toBind_549_, 2);
lean_inc_ref(v_inst_546_);
lean_inc(v_ex_548_);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__0), 4, 3);
lean_closure_set(v___f_550_, 0, v_ex_548_);
lean_closure_set(v___f_550_, 1, v_inst_545_);
lean_closure_set(v___f_550_, 2, v_inst_546_);
lean_inc_ref(v___f_550_);
lean_inc_ref(v_inst_547_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1), 4, 3);
lean_closure_set(v___f_551_, 0, v_inst_547_);
lean_closure_set(v___f_551_, 1, v_toBind_549_);
lean_closure_set(v___f_551_, 2, v___f_550_);
if (lean_obj_tag(v_ex_548_) == 16)
{
lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v___f_550_);
lean_dec_ref(v_inst_547_);
v___f_552_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__2), 2, 1);
lean_closure_set(v___f_552_, 0, v___f_551_);
v___x_553_ = l_Lean_throwInterruptException___redArg(v_inst_546_);
v___x_554_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v___x_553_, v___f_552_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___f_551_);
lean_dec(v_ex_548_);
lean_dec_ref(v_inst_546_);
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_throwKernelException___redArg___lam__1(v_inst_547_, v_toBind_549_, v___f_550_, v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object* v_m_557_, lean_object* v_00_u03b1_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_ex_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_throwKernelException___redArg(v_inst_559_, v_inst_560_, v_inst_561_, v_ex_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v_x_567_, 1);
v___x_569_ = l_Lean_throwKernelException___redArg(v_inst_564_, v_inst_565_, v_inst_566_, v_a_568_);
return v___x_569_;
}
else
{
lean_object* v_toApplicative_570_; lean_object* v_toPure_571_; lean_object* v_a_572_; lean_object* v___x_573_; 
v_toApplicative_570_ = lean_ctor_get(v_inst_564_, 0);
lean_inc_ref(v_toApplicative_570_);
lean_dec_ref(v_inst_566_);
lean_dec_ref(v_inst_565_);
lean_dec_ref(v_inst_564_);
v_toPure_571_ = lean_ctor_get(v_toApplicative_570_, 1);
lean_inc(v_toPure_571_);
lean_dec_ref(v_toApplicative_570_);
v_a_572_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v_x_567_, 1);
v___x_573_ = lean_apply_2(v_toPure_571_, lean_box(0), v_a_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object* v_m_574_, lean_object* v_00_u03b1_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_x_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_ofExceptKernelException___redArg(v_inst_576_, v_inst_577_, v_inst_578_, v_x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object* v_inst_581_, lean_object* v_00_u03b1_582_, lean_object* v_d_583_, lean_object* v_x_584_, lean_object* v_ctx_585_){
_start:
{
lean_object* v_withRecDepth_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_withRecDepth_586_ = lean_ctor_get(v_inst_581_, 0);
lean_inc(v_withRecDepth_586_);
lean_dec_ref(v_inst_581_);
v___x_587_ = lean_apply_1(v_x_584_, v_ctx_585_);
v___x_588_ = lean_apply_3(v_withRecDepth_586_, lean_box(0), v_d_583_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object* v_inst_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_getRecDepth_591_; 
v_getRecDepth_591_ = lean_ctor_get(v_inst_589_, 1);
lean_inc(v_getRecDepth_591_);
return v_getRecDepth_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object* v_inst_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_inst_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object* v_inst_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_getMaxRecDepth_597_; 
v_getMaxRecDepth_597_ = lean_ctor_get(v_inst_595_, 2);
lean_inc(v_getMaxRecDepth_597_);
return v_getMaxRecDepth_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object* v_inst_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec_ref(v_inst_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object* v_inst_601_){
_start:
{
lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; 
lean_inc_ref_n(v_inst_601_, 2);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_602_, 0, v_inst_601_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_603_, 0, v_inst_601_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_604_, 0, v_inst_601_);
v___x_605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_605_, 0, v___f_602_);
lean_ctor_set(v___x_605_, 1, v___f_603_);
lean_ctor_set(v___x_605_, 2, v___f_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object* v_m_606_, lean_object* v_00_u03c1_607_, lean_object* v_inst_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(lean_object* v_inst_610_, lean_object* v_d_611_, lean_object* v_x_612_, lean_object* v_ctx_613_){
_start:
{
lean_object* v_withRecDepth_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_withRecDepth_614_ = lean_ctor_get(v_inst_610_, 0);
lean_inc(v_withRecDepth_614_);
lean_dec_ref(v_inst_610_);
lean_inc(v_ctx_613_);
v___x_615_ = lean_apply_1(v_x_612_, v_ctx_613_);
v___x_616_ = lean_apply_3(v_withRecDepth_614_, lean_box(0), v_d_611_, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(lean_object* v_inst_617_, lean_object* v_d_618_, lean_object* v_x_619_, lean_object* v_ctx_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(v_inst_617_, v_d_618_, v_x_619_, v_ctx_620_);
lean_dec(v_ctx_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(lean_object* v_m_622_, lean_object* v_00_u03c9_623_, lean_object* v_00_u03c3_624_, lean_object* v_inst_625_, lean_object* v_00_u03b1_626_, lean_object* v_d_627_, lean_object* v_x_628_, lean_object* v_ctx_629_){
_start:
{
lean_object* v_withRecDepth_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_withRecDepth_630_ = lean_ctor_get(v_inst_625_, 0);
lean_inc(v_withRecDepth_630_);
lean_dec_ref(v_inst_625_);
lean_inc(v_ctx_629_);
v___x_631_ = lean_apply_1(v_x_628_, v_ctx_629_);
v___x_632_ = lean_apply_3(v_withRecDepth_630_, lean_box(0), v_d_627_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(lean_object* v_m_633_, lean_object* v_00_u03c9_634_, lean_object* v_00_u03c3_635_, lean_object* v_inst_636_, lean_object* v_00_u03b1_637_, lean_object* v_d_638_, lean_object* v_x_639_, lean_object* v_ctx_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(v_m_633_, v_00_u03c9_634_, v_00_u03c3_635_, v_inst_636_, v_00_u03b1_637_, v_d_638_, v_x_639_, v_ctx_640_);
lean_dec(v_ctx_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(lean_object* v_inst_642_){
_start:
{
lean_object* v_getRecDepth_643_; 
v_getRecDepth_643_ = lean_ctor_get(v_inst_642_, 1);
lean_inc(v_getRecDepth_643_);
return v_getRecDepth_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(lean_object* v_inst_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_644_);
lean_dec_ref(v_inst_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(lean_object* v_m_646_, lean_object* v_00_u03c9_647_, lean_object* v_00_u03c3_648_, lean_object* v_inst_649_, lean_object* v_x_650_){
_start:
{
lean_object* v_getRecDepth_651_; 
v_getRecDepth_651_ = lean_ctor_get(v_inst_649_, 1);
lean_inc(v_getRecDepth_651_);
return v_getRecDepth_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(lean_object* v_m_652_, lean_object* v_00_u03c9_653_, lean_object* v_00_u03c3_654_, lean_object* v_inst_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(v_m_652_, v_00_u03c9_653_, v_00_u03c3_654_, v_inst_655_, v_x_656_);
lean_dec(v_x_656_);
lean_dec_ref(v_inst_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(lean_object* v_inst_658_){
_start:
{
lean_object* v_getMaxRecDepth_659_; 
v_getMaxRecDepth_659_ = lean_ctor_get(v_inst_658_, 2);
lean_inc(v_getMaxRecDepth_659_);
return v_getMaxRecDepth_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(lean_object* v_inst_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_660_);
lean_dec_ref(v_inst_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(lean_object* v_m_662_, lean_object* v_00_u03c9_663_, lean_object* v_00_u03c3_664_, lean_object* v_inst_665_, lean_object* v_x_666_){
_start:
{
lean_object* v_getMaxRecDepth_667_; 
v_getMaxRecDepth_667_ = lean_ctor_get(v_inst_665_, 2);
lean_inc(v_getMaxRecDepth_667_);
return v_getMaxRecDepth_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(lean_object* v_m_668_, lean_object* v_00_u03c9_669_, lean_object* v_00_u03c3_670_, lean_object* v_inst_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(v_m_668_, v_00_u03c9_669_, v_00_u03c3_670_, v_inst_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec_ref(v_inst_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object* v_inst_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc_ref_n(v_inst_674_, 2);
v___x_675_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed), 8, 4);
lean_closure_set(v___x_675_, 0, lean_box(0));
lean_closure_set(v___x_675_, 1, lean_box(0));
lean_closure_set(v___x_675_, 2, lean_box(0));
lean_closure_set(v___x_675_, 3, v_inst_674_);
v___x_676_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed), 5, 4);
lean_closure_set(v___x_676_, 0, lean_box(0));
lean_closure_set(v___x_676_, 1, lean_box(0));
lean_closure_set(v___x_676_, 2, lean_box(0));
lean_closure_set(v___x_676_, 3, v_inst_674_);
v___x_677_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed), 5, 4);
lean_closure_set(v___x_677_, 0, lean_box(0));
lean_closure_set(v___x_677_, 1, lean_box(0));
lean_closure_set(v___x_677_, 2, lean_box(0));
lean_closure_set(v___x_677_, 3, v_inst_674_);
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v___x_675_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object* v_m_679_, lean_object* v_00_u03c9_680_, lean_object* v_00_u03c3_681_, lean_object* v_inst_682_, lean_object* v_inst_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object* v_m_685_, lean_object* v_00_u03c9_686_, lean_object* v_00_u03c3_687_, lean_object* v_inst_688_, lean_object* v_inst_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(v_m_685_, v_00_u03c9_686_, v_00_u03c3_687_, v_inst_688_, v_inst_689_);
lean_dec_ref(v_inst_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(lean_object* v_inst_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_withRecDepth_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_withRecDepth_695_ = lean_ctor_get(v_inst_691_, 0);
lean_inc(v_withRecDepth_695_);
lean_dec_ref(v_inst_691_);
lean_inc(v_a_694_);
v___x_696_ = lean_apply_1(v_a_693_, v_a_694_);
v___x_697_ = lean_apply_3(v_withRecDepth_695_, lean_box(0), v_a_692_, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(lean_object* v_inst_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(v_inst_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(lean_object* v_00_u03b1_703_, lean_object* v_m_704_, lean_object* v_00_u03c9_705_, lean_object* v_00_u03b2_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_00_u03b1_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_withRecDepth_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_withRecDepth_715_ = lean_ctor_get(v_inst_710_, 0);
lean_inc(v_withRecDepth_715_);
lean_dec_ref(v_inst_710_);
lean_inc(v_a_714_);
v___x_716_ = lean_apply_1(v_a_713_, v_a_714_);
v___x_717_ = lean_apply_3(v_withRecDepth_715_, lean_box(0), v_a_712_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(lean_object* v_00_u03b1_718_, lean_object* v_m_719_, lean_object* v_00_u03c9_720_, lean_object* v_00_u03b2_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_00_u03b1_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(v_00_u03b1_718_, v_m_719_, v_00_u03c9_720_, v_00_u03b2_721_, v_inst_722_, v_inst_723_, v_inst_724_, v_inst_725_, v_00_u03b1_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_inst_723_);
lean_dec_ref(v_inst_722_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(lean_object* v_inst_731_){
_start:
{
lean_object* v_getRecDepth_732_; 
v_getRecDepth_732_ = lean_ctor_get(v_inst_731_, 1);
lean_inc(v_getRecDepth_732_);
return v_getRecDepth_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(lean_object* v_inst_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_733_);
lean_dec_ref(v_inst_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(lean_object* v_00_u03b1_735_, lean_object* v_m_736_, lean_object* v_00_u03c9_737_, lean_object* v_00_u03b2_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_getRecDepth_744_; 
v_getRecDepth_744_ = lean_ctor_get(v_inst_742_, 1);
lean_inc(v_getRecDepth_744_);
return v_getRecDepth_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(lean_object* v_00_u03b1_745_, lean_object* v_m_746_, lean_object* v_00_u03c9_747_, lean_object* v_00_u03b2_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(v_00_u03b1_745_, v_m_746_, v_00_u03c9_747_, v_00_u03b2_748_, v_inst_749_, v_inst_750_, v_inst_751_, v_inst_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_inst_752_);
lean_dec_ref(v_inst_750_);
lean_dec_ref(v_inst_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(lean_object* v_inst_755_){
_start:
{
lean_object* v_getMaxRecDepth_756_; 
v_getMaxRecDepth_756_ = lean_ctor_get(v_inst_755_, 2);
lean_inc(v_getMaxRecDepth_756_);
return v_getMaxRecDepth_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(lean_object* v_inst_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_757_);
lean_dec_ref(v_inst_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(lean_object* v_00_u03b1_759_, lean_object* v_m_760_, lean_object* v_00_u03c9_761_, lean_object* v_00_u03b2_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_getMaxRecDepth_768_; 
v_getMaxRecDepth_768_ = lean_ctor_get(v_inst_766_, 2);
lean_inc(v_getMaxRecDepth_768_);
return v_getMaxRecDepth_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(lean_object* v_00_u03b1_769_, lean_object* v_m_770_, lean_object* v_00_u03c9_771_, lean_object* v_00_u03b2_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(v_00_u03b1_769_, v_m_770_, v_00_u03c9_771_, v_00_u03b2_772_, v_inst_773_, v_inst_774_, v_inst_775_, v_inst_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_inst_776_);
lean_dec_ref(v_inst_774_);
lean_dec_ref(v_inst_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_inc_ref_n(v_inst_782_, 2);
lean_inc_ref_n(v_inst_780_, 2);
lean_inc_ref_n(v_inst_779_, 2);
v___x_783_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed), 12, 8);
lean_closure_set(v___x_783_, 0, lean_box(0));
lean_closure_set(v___x_783_, 1, lean_box(0));
lean_closure_set(v___x_783_, 2, lean_box(0));
lean_closure_set(v___x_783_, 3, lean_box(0));
lean_closure_set(v___x_783_, 4, v_inst_779_);
lean_closure_set(v___x_783_, 5, v_inst_780_);
lean_closure_set(v___x_783_, 6, v_inst_781_);
lean_closure_set(v___x_783_, 7, v_inst_782_);
v___x_784_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed), 9, 8);
lean_closure_set(v___x_784_, 0, lean_box(0));
lean_closure_set(v___x_784_, 1, lean_box(0));
lean_closure_set(v___x_784_, 2, lean_box(0));
lean_closure_set(v___x_784_, 3, lean_box(0));
lean_closure_set(v___x_784_, 4, v_inst_779_);
lean_closure_set(v___x_784_, 5, v_inst_780_);
lean_closure_set(v___x_784_, 6, v_inst_781_);
lean_closure_set(v___x_784_, 7, v_inst_782_);
v___x_785_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed), 9, 8);
lean_closure_set(v___x_785_, 0, lean_box(0));
lean_closure_set(v___x_785_, 1, lean_box(0));
lean_closure_set(v___x_785_, 2, lean_box(0));
lean_closure_set(v___x_785_, 3, lean_box(0));
lean_closure_set(v___x_785_, 4, v_inst_779_);
lean_closure_set(v___x_785_, 5, v_inst_780_);
lean_closure_set(v___x_785_, 6, v_inst_781_);
lean_closure_set(v___x_785_, 7, v_inst_782_);
v___x_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object* v_00_u03b1_787_, lean_object* v_m_788_, lean_object* v_00_u03c9_789_, lean_object* v_00_u03b2_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(v_inst_791_, v_inst_792_, v_inst_794_, v_inst_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object* v_00_u03b1_797_, lean_object* v_m_798_, lean_object* v_00_u03c9_799_, lean_object* v_00_u03b2_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad(v_00_u03b1_797_, v_m_798_, v_00_u03c9_799_, v_00_u03b2_800_, v_inst_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_inst_805_);
lean_dec_ref(v_inst_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0(lean_object* v_withRecDepth_807_, lean_object* v_00_u03b1_808_, lean_object* v_d_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lean_apply_3(v_withRecDepth_807_, lean_box(0), v_d_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1(lean_object* v_toPure_812_, lean_object* v_____do__lift_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_____do__lift_813_);
v___x_815_ = lean_apply_2(v_toPure_812_, lean_box(0), v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg(lean_object* v_inst_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v_toApplicative_818_; lean_object* v_withRecDepth_819_; lean_object* v_getRecDepth_820_; lean_object* v_getMaxRecDepth_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_834_; 
v_toApplicative_818_ = lean_ctor_get(v_inst_816_, 0);
lean_inc_ref(v_toApplicative_818_);
v_withRecDepth_819_ = lean_ctor_get(v_inst_817_, 0);
v_getRecDepth_820_ = lean_ctor_get(v_inst_817_, 1);
v_getMaxRecDepth_821_ = lean_ctor_get(v_inst_817_, 2);
v_isSharedCheck_834_ = !lean_is_exclusive(v_inst_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_823_ = v_inst_817_;
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_getMaxRecDepth_821_);
lean_inc(v_getRecDepth_820_);
lean_inc(v_withRecDepth_819_);
lean_dec(v_inst_817_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_toBind_825_; lean_object* v_toPure_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_toBind_825_ = lean_ctor_get(v_inst_816_, 1);
lean_inc_n(v_toBind_825_, 2);
lean_dec_ref(v_inst_816_);
v_toPure_826_ = lean_ctor_get(v_toApplicative_818_, 1);
lean_inc(v_toPure_826_);
lean_dec_ref(v_toApplicative_818_);
v___f_827_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_827_, 0, v_withRecDepth_819_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_828_, 0, v_toPure_826_);
lean_inc_ref(v___f_828_);
v___x_829_ = lean_apply_4(v_toBind_825_, lean_box(0), lean_box(0), v_getRecDepth_820_, v___f_828_);
v___x_830_ = lean_apply_4(v_toBind_825_, lean_box(0), lean_box(0), v_getMaxRecDepth_821_, v___f_828_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 2, v___x_830_);
lean_ctor_set(v___x_823_, 1, v___x_829_);
lean_ctor_set(v___x_823_, 0, v___f_827_);
v___x_832_ = v___x_823_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___f_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad(lean_object* v_m_835_, lean_object* v_inst_836_, lean_object* v_inst_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_instMonadRecDepthOptionTOfMonad___redArg(v_inst_836_, v_inst_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = l_Lean_maxRecDepthErrorMessage;
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3);
v___x_847_ = l_Lean_MessageData_ofFormat(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4);
v___x_849_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_850_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object* v_inst_851_, lean_object* v_ref_852_){
_start:
{
lean_object* v_toMonadExceptOf_853_; lean_object* v_throw_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_863_; 
v_toMonadExceptOf_853_ = lean_ctor_get(v_inst_851_, 0);
lean_inc_ref(v_toMonadExceptOf_853_);
lean_dec_ref(v_inst_851_);
v_throw_854_ = lean_ctor_get(v_toMonadExceptOf_853_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_toMonadExceptOf_853_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_toMonadExceptOf_853_, 1);
lean_dec(v_unused_864_);
v___x_856_ = v_toMonadExceptOf_853_;
v_isShared_857_ = v_isSharedCheck_863_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_throw_854_);
lean_dec(v_toMonadExceptOf_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_863_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v___x_858_);
lean_ctor_set(v___x_856_, 0, v_ref_852_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_ref_852_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_apply_2(v_throw_854_, lean_box(0), v___x_860_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object* v_m_865_, lean_object* v_00_u03b1_866_, lean_object* v_inst_867_, lean_object* v_ref_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_867_, v_ref_868_);
return v___x_869_;
}
}
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object* v_ex_870_){
_start:
{
if (lean_obj_tag(v_ex_870_) == 0)
{
lean_object* v_msg_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_msg_871_ = lean_ctor_get(v_ex_870_, 1);
lean_inc_ref(v_msg_871_);
lean_dec_ref_known(v_ex_870_, 2);
v___x_872_ = l_Lean_MessageData_stripNestedTags(v_msg_871_);
v___x_873_ = l_Lean_MessageData_kind(v___x_872_);
lean_dec_ref(v___x_872_);
v___x_874_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_875_ = lean_name_eq(v___x_873_, v___x_874_);
lean_dec(v___x_873_);
return v___x_875_;
}
else
{
uint8_t v___x_876_; 
lean_dec_ref(v_ex_870_);
v___x_876_ = 0;
return v___x_876_;
}
}
}
LEAN_EXPORT void l_Lean_Exception_isMaxRecDepth_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_870_ = stack[0].m_obj;
uint8_t v_res_877_;
v_res_877_ = l_Lean_Exception_isMaxRecDepth(v_ex_870_);
stack->m_num = v_res_877_;
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object* v_ex_878_){
_start:
{
uint8_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l_Lean_Exception_isMaxRecDepth(v_ex_878_);
v_r_880_ = lean_box(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object* v_inst_881_, lean_object* v_____do__lift_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_881_, v_____do__lift_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object* v_curr_884_, lean_object* v_withRecDepth_885_, lean_object* v_x_886_, lean_object* v_toMonadRef_887_, lean_object* v_toBind_888_, lean_object* v___f_889_, lean_object* v_max_890_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v_max_890_, v___x_895_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; 
v___x_897_ = lean_nat_dec_eq(v_curr_884_, v_max_890_);
if (v___x_897_ == 0)
{
lean_dec(v___f_889_);
lean_dec(v_toBind_888_);
lean_dec_ref(v_toMonadRef_887_);
goto v___jp_891_;
}
else
{
lean_object* v_getRef_898_; lean_object* v___x_899_; 
lean_dec(v_x_886_);
lean_dec(v_withRecDepth_885_);
v_getRef_898_ = lean_ctor_get(v_toMonadRef_887_, 0);
lean_inc(v_getRef_898_);
lean_dec_ref(v_toMonadRef_887_);
v___x_899_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v_getRef_898_, v___f_889_);
return v___x_899_;
}
}
else
{
lean_dec(v___f_889_);
lean_dec(v_toBind_888_);
lean_dec_ref(v_toMonadRef_887_);
goto v___jp_891_;
}
v___jp_891_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_unsigned_to_nat(1u);
v___x_893_ = lean_nat_add(v_curr_884_, v___x_892_);
v___x_894_ = lean_apply_3(v_withRecDepth_885_, lean_box(0), v___x_893_, v_x_886_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object* v_curr_900_, lean_object* v_withRecDepth_901_, lean_object* v_x_902_, lean_object* v_toMonadRef_903_, lean_object* v_toBind_904_, lean_object* v___f_905_, lean_object* v_max_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_withIncRecDepth___redArg___lam__1(v_curr_900_, v_withRecDepth_901_, v_x_902_, v_toMonadRef_903_, v_toBind_904_, v___f_905_, v_max_906_);
lean_dec(v_max_906_);
lean_dec(v_curr_900_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object* v_withRecDepth_908_, lean_object* v_x_909_, lean_object* v_toMonadRef_910_, lean_object* v_toBind_911_, lean_object* v___f_912_, lean_object* v_getMaxRecDepth_913_, lean_object* v_curr_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; 
lean_inc(v_toBind_911_);
v___f_915_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_915_, 0, v_curr_914_);
lean_closure_set(v___f_915_, 1, v_withRecDepth_908_);
lean_closure_set(v___f_915_, 2, v_x_909_);
lean_closure_set(v___f_915_, 3, v_toMonadRef_910_);
lean_closure_set(v___f_915_, 4, v_toBind_911_);
lean_closure_set(v___f_915_, 5, v___f_912_);
v___x_916_ = lean_apply_4(v_toBind_911_, lean_box(0), lean_box(0), v_getMaxRecDepth_913_, v___f_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_x_920_){
_start:
{
lean_object* v_toBind_921_; lean_object* v_withRecDepth_922_; lean_object* v_getRecDepth_923_; lean_object* v_getMaxRecDepth_924_; lean_object* v_toMonadRef_925_; lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___x_928_; 
v_toBind_921_ = lean_ctor_get(v_inst_917_, 1);
lean_inc_n(v_toBind_921_, 2);
lean_dec_ref(v_inst_917_);
v_withRecDepth_922_ = lean_ctor_get(v_inst_919_, 0);
lean_inc(v_withRecDepth_922_);
v_getRecDepth_923_ = lean_ctor_get(v_inst_919_, 1);
lean_inc(v_getRecDepth_923_);
v_getMaxRecDepth_924_ = lean_ctor_get(v_inst_919_, 2);
lean_inc(v_getMaxRecDepth_924_);
lean_dec_ref(v_inst_919_);
v_toMonadRef_925_ = lean_ctor_get(v_inst_918_, 1);
lean_inc_ref(v_toMonadRef_925_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_926_, 0, v_inst_918_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_927_, 0, v_withRecDepth_922_);
lean_closure_set(v___f_927_, 1, v_x_920_);
lean_closure_set(v___f_927_, 2, v_toMonadRef_925_);
lean_closure_set(v___f_927_, 3, v_toBind_921_);
lean_closure_set(v___f_927_, 4, v___f_926_);
lean_closure_set(v___f_927_, 5, v_getMaxRecDepth_924_);
v___x_928_ = lean_apply_4(v_toBind_921_, lean_box(0), lean_box(0), v_getRecDepth_923_, v___f_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object* v_m_929_, lean_object* v_00_u03b1_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_toBind_935_; lean_object* v_withRecDepth_936_; lean_object* v_getRecDepth_937_; lean_object* v_getMaxRecDepth_938_; lean_object* v_toMonadRef_939_; lean_object* v___f_940_; lean_object* v___f_941_; lean_object* v___x_942_; 
v_toBind_935_ = lean_ctor_get(v_inst_931_, 1);
lean_inc_n(v_toBind_935_, 2);
lean_dec_ref(v_inst_931_);
v_withRecDepth_936_ = lean_ctor_get(v_inst_933_, 0);
lean_inc(v_withRecDepth_936_);
v_getRecDepth_937_ = lean_ctor_get(v_inst_933_, 1);
lean_inc(v_getRecDepth_937_);
v_getMaxRecDepth_938_ = lean_ctor_get(v_inst_933_, 2);
lean_inc(v_getMaxRecDepth_938_);
lean_dec_ref(v_inst_933_);
v_toMonadRef_939_ = lean_ctor_get(v_inst_932_, 1);
lean_inc_ref(v_toMonadRef_939_);
v___f_940_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_940_, 0, v_inst_932_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_941_, 0, v_withRecDepth_936_);
lean_closure_set(v___f_941_, 1, v_x_934_);
lean_closure_set(v___f_941_, 2, v_toMonadRef_939_);
lean_closure_set(v___f_941_, 3, v_toBind_935_);
lean_closure_set(v___f_941_, 4, v___f_940_);
lean_closure_set(v___f_941_, 5, v_getMaxRecDepth_938_);
v___x_942_ = lean_apply_4(v_toBind_935_, lean_box(0), lean_box(0), v_getRecDepth_937_, v___f_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6));
v___x_1027_ = l_String_toRawSubstring_x27(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23));
v___x_1064_ = l_String_toRawSubstring_x27(v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object* v_x_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_termThrowError_____00__closed__2));
lean_inc(v_x_1078_);
v___x_1082_ = l_Lean_Syntax_isOfKind(v_x_1078_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_x_1078_);
v___x_1083_ = lean_box(1);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1080_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = l_Lean_Syntax_getArg(v_x_1078_, v___x_1085_);
lean_dec(v_x_1078_);
v___x_1087_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1086_);
v___x_1088_ = l_Lean_Syntax_isOfKind(v___x_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v_quotContext_1089_; lean_object* v_currMacroScope_1090_; lean_object* v_ref_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_quotContext_1089_ = lean_ctor_get(v_a_1079_, 1);
v_currMacroScope_1090_ = lean_ctor_get(v_a_1079_, 2);
v_ref_1091_ = lean_ctor_get(v_a_1079_, 5);
v___x_1092_ = l_Lean_SourceInfo_fromRef(v_ref_1091_, v___x_1088_);
v___x_1093_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1094_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1095_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc(v_currMacroScope_1090_);
lean_inc(v_quotContext_1089_);
v___x_1096_ = l_Lean_addMacroScope(v_quotContext_1089_, v___x_1095_, v_currMacroScope_1090_);
v___x_1097_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1092_, 2);
v___x_1098_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1092_);
lean_ctor_set(v___x_1098_, 1, v___x_1094_);
lean_ctor_set(v___x_1098_, 2, v___x_1096_);
lean_ctor_set(v___x_1098_, 3, v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1100_ = l_Lean_Syntax_node1(v___x_1092_, v___x_1099_, v___x_1086_);
v___x_1101_ = l_Lean_Syntax_node2(v___x_1092_, v___x_1093_, v___x_1098_, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_a_1080_);
return v___x_1102_;
}
else
{
lean_object* v_quotContext_1103_; lean_object* v_currMacroScope_1104_; lean_object* v_ref_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_quotContext_1103_ = lean_ctor_get(v_a_1079_, 1);
v_currMacroScope_1104_ = lean_ctor_get(v_a_1079_, 2);
v_ref_1105_ = lean_ctor_get(v_a_1079_, 5);
v___x_1106_ = 0;
v___x_1107_ = l_Lean_SourceInfo_fromRef(v_ref_1105_, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1109_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1110_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc_n(v_currMacroScope_1104_, 2);
lean_inc_n(v_quotContext_1103_, 2);
v___x_1111_ = l_Lean_addMacroScope(v_quotContext_1103_, v___x_1110_, v_currMacroScope_1104_);
v___x_1112_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1107_, 10);
v___x_1113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1107_);
lean_ctor_set(v___x_1113_, 1, v___x_1109_);
lean_ctor_set(v___x_1113_, 2, v___x_1111_);
lean_ctor_set(v___x_1113_, 3, v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1115_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1116_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1117_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1107_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1120_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Lean_addMacroScope(v_quotContext_1103_, v___x_1121_, v_currMacroScope_1104_);
v___x_1123_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1124_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1107_);
lean_ctor_set(v___x_1124_, 1, v___x_1120_);
lean_ctor_set(v___x_1124_, 2, v___x_1122_);
lean_ctor_set(v___x_1124_, 3, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_node1(v___x_1107_, v___x_1119_, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1116_, v___x_1118_, v___x_1125_);
v___x_1127_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1128_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1107_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1127_, v___x_1129_, v___x_1086_);
v___x_1131_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1107_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_Syntax_node3(v___x_1107_, v___x_1115_, v___x_1126_, v___x_1130_, v___x_1132_);
v___x_1134_ = l_Lean_Syntax_node1(v___x_1107_, v___x_1114_, v___x_1133_);
v___x_1135_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1108_, v___x_1113_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_a_1080_);
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(lean_object* v_x_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(v_x_1137_, v_a_1138_, v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1140_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0));
v___x_1143_ = l_String_toRawSubstring_x27(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_termThrowErrorAt_________00__closed__1));
lean_inc(v_x_1154_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_x_1154_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v_x_1154_);
v___x_1159_ = lean_box(1);
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_a_1156_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = l_Lean_Syntax_getArg(v_x_1154_, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(2u);
v___x_1164_ = l_Lean_Syntax_getArg(v_x_1154_, v___x_1163_);
lean_dec(v_x_1154_);
v___x_1165_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1164_);
v___x_1166_ = l_Lean_Syntax_isOfKind(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v_quotContext_1167_; lean_object* v_currMacroScope_1168_; lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_quotContext_1167_ = lean_ctor_get(v_a_1155_, 1);
v_currMacroScope_1168_ = lean_ctor_get(v_a_1155_, 2);
v_ref_1169_ = lean_ctor_get(v_a_1155_, 5);
v___x_1170_ = l_Lean_SourceInfo_fromRef(v_ref_1169_, v___x_1166_);
v___x_1171_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1172_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1173_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc(v_currMacroScope_1168_);
lean_inc(v_quotContext_1167_);
v___x_1174_ = l_Lean_addMacroScope(v_quotContext_1167_, v___x_1173_, v_currMacroScope_1168_);
v___x_1175_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1170_, 2);
v___x_1176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1170_);
lean_ctor_set(v___x_1176_, 1, v___x_1172_);
lean_ctor_set(v___x_1176_, 2, v___x_1174_);
lean_ctor_set(v___x_1176_, 3, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1178_ = l_Lean_Syntax_node2(v___x_1170_, v___x_1177_, v___x_1162_, v___x_1164_);
v___x_1179_ = l_Lean_Syntax_node2(v___x_1170_, v___x_1171_, v___x_1176_, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_a_1156_);
return v___x_1180_;
}
else
{
lean_object* v_quotContext_1181_; lean_object* v_currMacroScope_1182_; lean_object* v_ref_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_quotContext_1181_ = lean_ctor_get(v_a_1155_, 1);
v_currMacroScope_1182_ = lean_ctor_get(v_a_1155_, 2);
v_ref_1183_ = lean_ctor_get(v_a_1155_, 5);
v___x_1184_ = 0;
v___x_1185_ = l_Lean_SourceInfo_fromRef(v_ref_1183_, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1187_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1188_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc_n(v_currMacroScope_1182_, 2);
lean_inc_n(v_quotContext_1181_, 2);
v___x_1189_ = l_Lean_addMacroScope(v_quotContext_1181_, v___x_1188_, v_currMacroScope_1182_);
v___x_1190_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1185_, 10);
v___x_1191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1185_);
lean_ctor_set(v___x_1191_, 1, v___x_1187_);
lean_ctor_set(v___x_1191_, 2, v___x_1189_);
lean_ctor_set(v___x_1191_, 3, v___x_1190_);
v___x_1192_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1193_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1194_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1195_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1185_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1198_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1199_ = lean_box(0);
v___x_1200_ = l_Lean_addMacroScope(v_quotContext_1181_, v___x_1199_, v_currMacroScope_1182_);
v___x_1201_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1185_);
lean_ctor_set(v___x_1202_, 1, v___x_1198_);
lean_ctor_set(v___x_1202_, 2, v___x_1200_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
v___x_1203_ = l_Lean_Syntax_node1(v___x_1185_, v___x_1197_, v___x_1202_);
v___x_1204_ = l_Lean_Syntax_node2(v___x_1185_, v___x_1194_, v___x_1196_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1206_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1185_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_Syntax_node2(v___x_1185_, v___x_1205_, v___x_1207_, v___x_1164_);
v___x_1209_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1185_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = l_Lean_Syntax_node3(v___x_1185_, v___x_1193_, v___x_1204_, v___x_1208_, v___x_1210_);
v___x_1212_ = l_Lean_Syntax_node2(v___x_1185_, v___x_1192_, v___x_1162_, v___x_1211_);
v___x_1213_ = l_Lean_Syntax_node2(v___x_1185_, v___x_1186_, v___x_1191_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v_a_1156_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(lean_object* v_x_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(v_x_1215_, v_a_1216_, v_a_1217_);
lean_dec_ref(v_a_1216_);
return v_res_1218_;
}
}
lean_object* runtime_initialize_Lean_InternalExceptionId(uint8_t builtin);
lean_object* runtime_initialize_Lean_ErrorExplanation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Exception(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_InternalExceptionId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedException = _init_l_Lean_instInhabitedException();
lean_mark_persistent(l_Lean_instInhabitedException);
l_Lean_unknownIdentifierMessageTag = _init_l_Lean_unknownIdentifierMessageTag();
lean_mark_persistent(l_Lean_unknownIdentifierMessageTag);
res = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_interruptExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_interruptExceptionId);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Exception(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin);
lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Exception(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_InternalExceptionId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Exception(builtin);
}
#ifdef __cplusplus
}
#endif
