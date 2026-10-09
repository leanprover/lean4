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
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object* v_x_47_){
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
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_Exception_hasSyntheticSorry(v_x_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_getRef(lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_ref_55_; 
v_ref_55_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_ref_55_);
return v_ref_55_;
}
else
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_getRef___boxed(lean_object* v_x_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Exception_getRef(v_x_57_);
lean_dec_ref(v_x_57_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_instInhabitedException___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = l_Lean_instInhabitedMessageData_default;
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_instInhabitedException(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Lean_instInhabitedException___closed__0, &l_Lean_instInhabitedException___closed__0_once, _init_l_Lean_instInhabitedException___closed__0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(lean_object* v_ref_63_, lean_object* v_toPure_64_, lean_object* v_msg_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_ref_63_);
lean_ctor_set(v___x_66_, 1, v_msg_65_);
v___x_67_ = lean_apply_2(v_toPure_64_, lean_box(0), v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(lean_object* v_toPure_68_, lean_object* v_inst_69_, lean_object* v_toBind_70_, lean_object* v_ref_71_, lean_object* v_msg_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___f_73_ = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_73_, 0, v_ref_71_);
lean_closure_set(v___f_73_, 1, v_toPure_68_);
v___x_74_ = lean_apply_1(v_inst_69_, v_msg_72_);
v___x_75_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_74_, v___f_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object* v_inst_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v_toApplicative_78_; lean_object* v_toBind_79_; lean_object* v_toPure_80_; lean_object* v___f_81_; 
v_toApplicative_78_ = lean_ctor_get(v_inst_77_, 0);
lean_inc_ref(v_toApplicative_78_);
v_toBind_79_ = lean_ctor_get(v_inst_77_, 1);
lean_inc(v_toBind_79_);
lean_dec_ref(v_inst_77_);
v_toPure_80_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_80_);
lean_dec_ref(v_toApplicative_78_);
v___f_81_ = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_81_, 0, v_toPure_80_);
lean_closure_set(v___f_81_, 1, v_inst_76_);
lean_closure_set(v___f_81_, 2, v_toBind_79_);
return v___f_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_object* v_m_82_, lean_object* v_inst_83_, lean_object* v_inst_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v_inst_83_, v_inst_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0(lean_object* v_toMonadExceptOf_86_, lean_object* v_____x_87_){
_start:
{
lean_object* v_fst_88_; lean_object* v_snd_89_; lean_object* v_throw_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_98_; 
v_fst_88_ = lean_ctor_get(v_____x_87_, 0);
v_snd_89_ = lean_ctor_get(v_____x_87_, 1);
v_throw_90_ = lean_ctor_get(v_toMonadExceptOf_86_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_toMonadExceptOf_86_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v_toMonadExceptOf_86_, 1);
lean_dec(v_unused_99_);
v___x_92_ = v_toMonadExceptOf_86_;
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_throw_90_);
lean_dec(v_toMonadExceptOf_86_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
lean_inc(v_snd_89_);
lean_inc(v_fst_88_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v_snd_89_);
lean_ctor_set(v___x_92_, 0, v_fst_88_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_fst_88_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_snd_89_);
v___x_95_ = v_reuseFailAlloc_97_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; 
v___x_96_ = lean_apply_2(v_throw_90_, lean_box(0), v___x_95_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0___boxed(lean_object* v_toMonadExceptOf_100_, lean_object* v_____x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_throwError___redArg___lam__0(v_toMonadExceptOf_100_, v_____x_101_);
lean_dec_ref(v_____x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__1(lean_object* v_toAddErrorMessageContext_103_, lean_object* v_msg_104_, lean_object* v_toBind_105_, lean_object* v___f_106_, lean_object* v_ref_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_apply_2(v_toAddErrorMessageContext_103_, v_ref_107_, v_msg_104_);
v___x_109_ = lean_apply_4(v_toBind_105_, lean_box(0), lean_box(0), v___x_108_, v___f_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg(lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_msg_112_){
_start:
{
lean_object* v_toMonadRef_113_; lean_object* v_toBind_114_; lean_object* v_toMonadExceptOf_115_; lean_object* v_toAddErrorMessageContext_116_; lean_object* v_getRef_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_toMonadRef_113_ = lean_ctor_get(v_inst_111_, 1);
lean_inc_ref(v_toMonadRef_113_);
v_toBind_114_ = lean_ctor_get(v_inst_110_, 1);
lean_inc_n(v_toBind_114_, 2);
lean_dec_ref(v_inst_110_);
v_toMonadExceptOf_115_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref(v_toMonadExceptOf_115_);
v_toAddErrorMessageContext_116_ = lean_ctor_get(v_inst_111_, 2);
lean_inc(v_toAddErrorMessageContext_116_);
lean_dec_ref(v_inst_111_);
v_getRef_117_ = lean_ctor_get(v_toMonadRef_113_, 0);
lean_inc(v_getRef_117_);
lean_dec_ref(v_toMonadRef_113_);
v___f_118_ = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_118_, 0, v_toMonadExceptOf_115_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__1), 5, 4);
lean_closure_set(v___f_119_, 0, v_toAddErrorMessageContext_116_);
lean_closure_set(v___f_119_, 1, v_msg_112_);
lean_closure_set(v___f_119_, 2, v_toBind_114_);
lean_closure_set(v___f_119_, 3, v___f_118_);
v___x_120_ = lean_apply_4(v_toBind_114_, lean_box(0), lean_box(0), v_getRef_117_, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError(lean_object* v_m_121_, lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_msg_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_throwError___redArg(v_inst_123_, v_inst_124_, v_msg_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_unknownIdentifierMessageTag___closed__2));
v___x_133_ = l_Lean_kindOfErrorName(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_unknownIdentifierMessageTag___closed__3, &l_Lean_unknownIdentifierMessageTag___closed__3_once, _init_l_Lean_unknownIdentifierMessageTag___closed__3);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0(lean_object* v_ref_135_, lean_object* v_withRef_136_, lean_object* v___x_137_, lean_object* v_oldRef_138_){
_start:
{
lean_object* v_ref_139_; lean_object* v___x_140_; 
v_ref_139_ = l_Lean_replaceRef(v_ref_135_, v_oldRef_138_);
v___x_140_ = lean_apply_3(v_withRef_136_, lean_box(0), v_ref_139_, v___x_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0___boxed(lean_object* v_ref_141_, lean_object* v_withRef_142_, lean_object* v___x_143_, lean_object* v_oldRef_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwErrorAt___redArg___lam__0(v_ref_141_, v_withRef_142_, v___x_143_, v_oldRef_144_);
lean_dec(v_oldRef_144_);
lean_dec(v_ref_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_ref_148_, lean_object* v_msg_149_){
_start:
{
lean_object* v_toMonadRef_150_; lean_object* v_toBind_151_; lean_object* v_getRef_152_; lean_object* v_withRef_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___x_156_; 
v_toMonadRef_150_ = lean_ctor_get(v_inst_147_, 1);
v_toBind_151_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_toBind_151_);
v_getRef_152_ = lean_ctor_get(v_toMonadRef_150_, 0);
lean_inc(v_getRef_152_);
v_withRef_153_ = lean_ctor_get(v_toMonadRef_150_, 1);
lean_inc(v_withRef_153_);
v___x_154_ = l_Lean_throwError___redArg(v_inst_146_, v_inst_147_, v_msg_149_);
v___f_155_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_155_, 0, v_ref_148_);
lean_closure_set(v___f_155_, 1, v_withRef_153_);
lean_closure_set(v___f_155_, 2, v___x_154_);
v___x_156_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v_getRef_152_, v___f_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt(lean_object* v_m_157_, lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_ref_161_, lean_object* v_msg_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_throwErrorAt___redArg(v_inst_159_, v_inst_160_, v_ref_161_, v_msg_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg___lam__1(lean_object* v_msg_164_, lean_object* v_name_165_, lean_object* v_toAddErrorMessageContext_166_, lean_object* v_toBind_167_, lean_object* v___f_168_, lean_object* v_ref_169_){
_start:
{
lean_object* v_msg_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_msg_170_ = l_Lean_MessageData_tagWithErrorName(v_msg_164_, v_name_165_);
v___x_171_ = lean_apply_2(v_toAddErrorMessageContext_166_, v_ref_169_, v_msg_170_);
v___x_172_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_171_, v___f_168_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_name_175_, lean_object* v_msg_176_){
_start:
{
lean_object* v_toMonadRef_177_; lean_object* v_toBind_178_; lean_object* v_toMonadExceptOf_179_; lean_object* v_toAddErrorMessageContext_180_; lean_object* v_getRef_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v_toMonadRef_177_ = lean_ctor_get(v_inst_174_, 1);
lean_inc_ref(v_toMonadRef_177_);
v_toBind_178_ = lean_ctor_get(v_inst_173_, 1);
lean_inc_n(v_toBind_178_, 2);
lean_dec_ref(v_inst_173_);
v_toMonadExceptOf_179_ = lean_ctor_get(v_inst_174_, 0);
lean_inc_ref(v_toMonadExceptOf_179_);
v_toAddErrorMessageContext_180_ = lean_ctor_get(v_inst_174_, 2);
lean_inc(v_toAddErrorMessageContext_180_);
lean_dec_ref(v_inst_174_);
v_getRef_181_ = lean_ctor_get(v_toMonadRef_177_, 0);
lean_inc(v_getRef_181_);
lean_dec_ref(v_toMonadRef_177_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_182_, 0, v_toMonadExceptOf_179_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_throwNamedError___redArg___lam__1), 6, 5);
lean_closure_set(v___f_183_, 0, v_msg_176_);
lean_closure_set(v___f_183_, 1, v_name_175_);
lean_closure_set(v___f_183_, 2, v_toAddErrorMessageContext_180_);
lean_closure_set(v___f_183_, 3, v_toBind_178_);
lean_closure_set(v___f_183_, 4, v___f_182_);
v___x_184_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v_getRef_181_, v___f_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError(lean_object* v_m_185_, lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_name_189_, lean_object* v_msg_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_throwNamedError___redArg(v_inst_187_, v_inst_188_, v_name_189_, v_msg_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_ref_194_, lean_object* v_name_195_, lean_object* v_msg_196_){
_start:
{
lean_object* v_toMonadRef_197_; lean_object* v_toBind_198_; lean_object* v_getRef_199_; lean_object* v_withRef_200_; lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_toMonadRef_197_ = lean_ctor_get(v_inst_193_, 1);
v_toBind_198_ = lean_ctor_get(v_inst_192_, 1);
lean_inc(v_toBind_198_);
v_getRef_199_ = lean_ctor_get(v_toMonadRef_197_, 0);
lean_inc(v_getRef_199_);
v_withRef_200_ = lean_ctor_get(v_toMonadRef_197_, 1);
lean_inc(v_withRef_200_);
v___x_201_ = l_Lean_throwNamedError___redArg(v_inst_192_, v_inst_193_, v_name_195_, v_msg_196_);
v___f_202_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_202_, 0, v_ref_194_);
lean_closure_set(v___f_202_, 1, v_withRef_200_);
lean_closure_set(v___f_202_, 2, v___x_201_);
v___x_203_ = lean_apply_4(v_toBind_198_, lean_box(0), lean_box(0), v_getRef_199_, v___f_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt(lean_object* v_m_204_, lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_ref_208_, lean_object* v_name_209_, lean_object* v_msg_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_throwNamedErrorAt___redArg(v_inst_206_, v_inst_207_, v_ref_208_, v_name_209_, v_msg_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
lean_ctor_set(v___x_218_, 3, v___x_217_);
lean_ctor_set(v___x_218_, 4, v___x_216_);
lean_ctor_set(v___x_218_, 5, v___x_216_);
lean_ctor_set(v___x_218_, 6, v___x_216_);
lean_ctor_set(v___x_218_, 7, v___x_216_);
lean_ctor_set(v___x_218_, 8, v___x_216_);
lean_ctor_set(v___x_218_, 9, v___x_216_);
lean_ctor_set(v___x_218_, 10, v___x_216_);
lean_ctor_set(v___x_218_, 11, v___x_215_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(32u);
v___x_220_ = lean_mk_empty_array_with_capacity(v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4(void){
_start:
{
size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_unsigned_to_nat(32u);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
v___x_226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3);
v___x_227_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_223_);
lean_ctor_set(v___x_227_, 3, v___x_223_);
lean_ctor_set_usize(v___x_227_, 4, v___x_222_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_box(1);
v___x_229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4);
v___x_230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_228_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__20));
v___x_255_ = l_Lean_stringToMessageData(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__22));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__24));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__26));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object* v_declHint_265_, lean_object* v_toPure_266_, lean_object* v_msg_267_, lean_object* v___x_268_, lean_object* v_env_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Lean_Name_isAnonymous(v_declHint_265_);
if (v___x_270_ == 0)
{
uint8_t v_isExporting_271_; 
v_isExporting_271_ = lean_ctor_get_uint8(v_env_269_, sizeof(void*)*13);
if (v_isExporting_271_ == 0)
{
lean_object* v___x_272_; 
lean_dec_ref(v_env_269_);
lean_dec(v_declHint_265_);
v___x_272_ = lean_apply_2(v_toPure_266_, lean_box(0), v_msg_267_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; uint8_t v___x_274_; 
lean_inc_ref(v_env_269_);
v___x_273_ = l_Lean_Environment_setExporting(v_env_269_, v___x_270_);
lean_inc(v_declHint_265_);
lean_inc_ref(v___x_273_);
v___x_274_ = l_Lean_Environment_contains(v___x_273_, v_declHint_265_, v_isExporting_271_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec_ref(v___x_273_);
lean_dec_ref(v_env_269_);
lean_dec(v_declHint_265_);
v___x_275_ = lean_apply_2(v_toPure_266_, lean_box(0), v_msg_267_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_c_281_; lean_object* v___x_282_; 
v___x_276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2);
v___x_277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5);
v___x_278_ = l_Lean_Options_empty;
v___x_279_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_279_, 0, v___x_273_);
lean_ctor_set(v___x_279_, 1, v___x_276_);
lean_ctor_set(v___x_279_, 2, v___x_277_);
lean_ctor_set(v___x_279_, 3, v___x_278_);
lean_inc(v_declHint_265_);
v___x_280_ = l_Lean_MessageData_ofConstName(v_declHint_265_, v___x_270_);
v_c_281_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_281_, 0, v___x_279_);
lean_ctor_set(v_c_281_, 1, v___x_280_);
v___x_282_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_269_, v_declHint_265_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref(v_env_269_);
lean_dec(v_declHint_265_);
v___x_283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_c_281_);
v___x_285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_MessageData_note(v___x_286_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v_msg_267_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_288_);
return v___x_289_;
}
else
{
lean_object* v_val_290_; lean_object* v___x_291_; lean_object* v_modules_292_; lean_object* v_moduleNames_293_; lean_object* v_mod_294_; uint8_t v___y_296_; uint8_t v___x_322_; 
v_val_290_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v___x_282_, 1);
v___x_291_ = l_Lean_Environment_header(v_env_269_);
lean_dec_ref(v_env_269_);
v_modules_292_ = lean_ctor_get(v___x_291_, 3);
lean_inc_ref(v_modules_292_);
v_moduleNames_293_ = lean_ctor_get(v___x_291_, 4);
lean_inc_ref(v_moduleNames_293_);
lean_dec_ref(v___x_291_);
v_mod_294_ = lean_array_get(v___x_268_, v_moduleNames_293_, v_val_290_);
lean_dec_ref(v_moduleNames_293_);
v___x_322_ = l_Lean_isPrivateName(v_declHint_265_);
lean_dec(v_declHint_265_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_modules_292_);
v___x_324_ = lean_nat_dec_lt(v_val_290_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_modules_292_);
lean_dec(v_val_290_);
v___y_296_ = v___x_322_;
goto v___jp_295_;
}
else
{
lean_object* v___x_325_; lean_object* v_toImport_326_; uint8_t v_isExported_327_; 
v___x_325_ = lean_array_fget(v_modules_292_, v_val_290_);
lean_dec(v_val_290_);
lean_dec_ref(v_modules_292_);
v_toImport_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_toImport_326_);
lean_dec(v___x_325_);
v_isExported_327_ = lean_ctor_get_uint8(v_toImport_326_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_326_);
v___y_296_ = v_isExported_327_;
goto v___jp_295_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_modules_292_);
lean_dec(v_val_290_);
v___x_328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_c_281_);
v___x_330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__25);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Lean_MessageData_ofName(v_mod_294_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__27);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = l_Lean_MessageData_note(v___x_335_);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v_msg_267_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_337_);
return v___x_338_;
}
v___jp_295_:
{
if (v___y_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_c_281_);
v___x_299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_MessageData_ofName(v_mod_294_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_MessageData_note(v___x_304_);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v_msg_267_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17);
v___x_309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_c_281_);
v___x_310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Lean_MessageData_ofName(v_mod_294_);
lean_inc_ref(v___x_312_);
v___x_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__21);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_312_);
v___x_317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__23);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_MessageData_note(v___x_318_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v_msg_267_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_apply_2(v_toPure_266_, lean_box(0), v___x_320_);
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v___x_339_; 
lean_dec_ref(v_env_269_);
lean_dec(v_declHint_265_);
v___x_339_ = lean_apply_2(v_toPure_266_, lean_box(0), v_msg_267_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed(lean_object* v_declHint_340_, lean_object* v_toPure_341_, lean_object* v_msg_342_, lean_object* v___x_343_, lean_object* v_env_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(v_declHint_340_, v_toPure_341_, v_msg_342_, v___x_343_, v_env_344_);
lean_dec(v___x_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg(lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_msg_348_, lean_object* v_declHint_349_){
_start:
{
lean_object* v_toApplicative_350_; lean_object* v_toBind_351_; lean_object* v_getEnv_352_; lean_object* v_toPure_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___x_356_; 
v_toApplicative_350_ = lean_ctor_get(v_inst_346_, 0);
lean_inc_ref(v_toApplicative_350_);
v_toBind_351_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_toBind_351_);
lean_dec_ref(v_inst_346_);
v_getEnv_352_ = lean_ctor_get(v_inst_347_, 0);
lean_inc(v_getEnv_352_);
lean_dec_ref(v_inst_347_);
v_toPure_353_ = lean_ctor_get(v_toApplicative_350_, 1);
lean_inc(v_toPure_353_);
lean_dec_ref(v_toApplicative_350_);
v___x_354_ = lean_box(0);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_355_, 0, v_declHint_349_);
lean_closure_set(v___f_355_, 1, v_toPure_353_);
lean_closure_set(v___f_355_, 2, v_msg_348_);
lean_closure_set(v___f_355_, 3, v___x_354_);
v___x_356_ = lean_apply_4(v_toBind_351_, lean_box(0), lean_box(0), v_getEnv_352_, v___f_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore(lean_object* v_m_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_msg_361_, lean_object* v_declHint_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_358_, v_inst_359_, v_msg_361_, v_declHint_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___boxed(lean_object* v_m_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_msg_368_, lean_object* v_declHint_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_mkUnknownIdentifierMessageCore(v_m_364_, v_inst_365_, v_inst_366_, v_inst_367_, v_msg_368_, v_declHint_369_);
lean_dec_ref(v_inst_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(lean_object* v_toPure_371_, lean_object* v_msg_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = l_Lean_unknownIdentifierMessageTag;
v___x_374_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_msg_372_);
v___x_375_ = lean_apply_2(v_toPure_371_, lean_box(0), v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_msg_378_, lean_object* v_declHint_379_){
_start:
{
lean_object* v_toApplicative_380_; lean_object* v_toBind_381_; lean_object* v_toPure_382_; lean_object* v___x_383_; lean_object* v___f_384_; lean_object* v___x_385_; 
v_toApplicative_380_ = lean_ctor_get(v_inst_376_, 0);
v_toBind_381_ = lean_ctor_get(v_inst_376_, 1);
lean_inc(v_toBind_381_);
v_toPure_382_ = lean_ctor_get(v_toApplicative_380_, 1);
lean_inc(v_toPure_382_);
v___x_383_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_376_, v_inst_377_, v_msg_378_, v_declHint_379_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_384_, 0, v_toPure_382_);
v___x_385_ = lean_apply_4(v_toBind_381_, lean_box(0), lean_box(0), v___x_383_, v___f_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object* v_m_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_msg_390_, lean_object* v_declHint_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_387_, v_inst_388_, v_msg_390_, v_declHint_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___boxed(lean_object* v_m_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_msg_397_, lean_object* v_declHint_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_mkUnknownIdentifierMessage(v_m_393_, v_inst_394_, v_inst_395_, v_inst_396_, v_msg_397_, v_declHint_398_);
lean_dec_ref(v_inst_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg___lam__0(lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_ref_402_, lean_object* v_____do__lift_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_throwErrorAt___redArg(v_inst_400_, v_inst_401_, v_ref_402_, v_____do__lift_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_ref_408_, lean_object* v_msg_409_, lean_object* v_declHint_410_){
_start:
{
lean_object* v_toBind_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_toBind_411_ = lean_ctor_get(v_inst_405_, 1);
lean_inc(v_toBind_411_);
lean_inc_ref(v_inst_405_);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_throwUnknownIdentifierAt___redArg___lam__0), 4, 3);
lean_closure_set(v___f_412_, 0, v_inst_405_);
lean_closure_set(v___f_412_, 1, v_inst_407_);
lean_closure_set(v___f_412_, 2, v_ref_408_);
v___x_413_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_405_, v_inst_406_, v_msg_409_, v_declHint_410_);
v___x_414_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v___x_413_, v___f_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object* v_m_415_, lean_object* v_00_u03b1_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_ref_420_, lean_object* v_msg_421_, lean_object* v_declHint_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_417_, v_inst_418_, v_inst_419_, v_ref_420_, v_msg_421_, v_declHint_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__0));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__2));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_ref_433_, lean_object* v_constName_434_){
_start:
{
lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_435_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__1, &l_Lean_throwUnknownConstantAt___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__1);
v___x_436_ = 0;
lean_inc(v_constName_434_);
v___x_437_ = l_Lean_MessageData_ofConstName(v_constName_434_, v___x_436_);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_435_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__3, &l_Lean_throwUnknownConstantAt___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__3);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_ref_433_, v___x_440_, v_constName_434_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object* v_m_442_, lean_object* v_00_u03b1_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_ref_447_, lean_object* v_constName_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_444_, v_inst_445_, v_inst_446_, v_ref_447_, v_constName_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_constName_453_, lean_object* v_____do__lift_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_450_, v_inst_451_, v_inst_452_, v_____do__lift_454_, v_constName_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_constName_459_){
_start:
{
lean_object* v_toMonadRef_460_; lean_object* v_toBind_461_; lean_object* v_getRef_462_; lean_object* v___f_463_; lean_object* v___x_464_; 
v_toMonadRef_460_ = lean_ctor_get(v_inst_458_, 1);
v_toBind_461_ = lean_ctor_get(v_inst_456_, 1);
lean_inc(v_toBind_461_);
v_getRef_462_ = lean_ctor_get(v_toMonadRef_460_, 0);
lean_inc(v_getRef_462_);
v___f_463_ = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___redArg___lam__0), 5, 4);
lean_closure_set(v___f_463_, 0, v_inst_456_);
lean_closure_set(v___f_463_, 1, v_inst_457_);
lean_closure_set(v___f_463_, 2, v_inst_458_);
lean_closure_set(v___f_463_, 3, v_constName_459_);
v___x_464_ = lean_apply_4(v_toBind_461_, lean_box(0), lean_box(0), v_getRef_462_, v___f_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object* v_m_465_, lean_object* v_00_u03b1_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_constName_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_throwUnknownConstant___redArg(v_inst_467_, v_inst_468_, v_inst_469_, v_constName_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_x_475_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_a_476_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_x_475_, 1);
v___x_477_ = lean_apply_1(v_inst_474_, v_a_476_);
v___x_478_ = l_Lean_throwError___redArg(v_inst_472_, v_inst_473_, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v_toApplicative_479_; lean_object* v_toPure_480_; lean_object* v_a_481_; lean_object* v___x_482_; 
v_toApplicative_479_ = lean_ctor_get(v_inst_472_, 0);
lean_inc_ref(v_toApplicative_479_);
lean_dec_ref(v_inst_474_);
lean_dec_ref(v_inst_473_);
lean_dec_ref(v_inst_472_);
v_toPure_480_ = lean_ctor_get(v_toApplicative_479_, 1);
lean_inc(v_toPure_480_);
lean_dec_ref(v_toApplicative_479_);
v_a_481_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_x_475_, 1);
v___x_482_ = lean_apply_2(v_toPure_480_, lean_box(0), v_a_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object* v_m_483_, lean_object* v_00_u03b5_484_, lean_object* v_00_u03b1_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_ofExcept___redArg(v_inst_486_, v_inst_487_, v_inst_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_));
v___x_496_ = l_Lean_registerInternalExceptionId(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
return v_res_498_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_box(0);
v___x_500_ = l_Lean_interruptExceptionId;
v___x_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object* v_inst_502_){
_start:
{
lean_object* v_toMonadExceptOf_503_; lean_object* v_throw_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_toMonadExceptOf_503_ = lean_ctor_get(v_inst_502_, 0);
lean_inc_ref(v_toMonadExceptOf_503_);
lean_dec_ref(v_inst_502_);
v_throw_504_ = lean_ctor_get(v_toMonadExceptOf_503_, 0);
lean_inc(v_throw_504_);
lean_dec_ref(v_toMonadExceptOf_503_);
v___x_505_ = lean_obj_once(&l_Lean_throwInterruptException___redArg___closed__0, &l_Lean_throwInterruptException___redArg___closed__0_once, _init_l_Lean_throwInterruptException___redArg___closed__0);
v___x_506_ = lean_apply_2(v_throw_504_, lean_box(0), v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object* v_m_507_, lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_throwInterruptException___redArg(v_inst_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object* v_m_513_, lean_object* v_00_u03b1_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_throwInterruptException(v_m_513_, v_00_u03b1_514_, v_inst_515_, v_inst_516_, v_inst_517_);
lean_dec_ref(v_inst_517_);
lean_dec_ref(v_inst_515_);
return v_res_518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 1)
{
lean_object* v_id_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_id_520_ = lean_ctor_get(v_x_519_, 0);
v___x_521_ = l_Lean_interruptExceptionId;
v___x_522_ = l_Lean_instBEqInternalExceptionId_beq(v_id_520_, v___x_521_);
return v___x_522_;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = 0;
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object* v_x_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lean_Exception_isInterrupt(v_x_524_);
lean_dec_ref(v_x_524_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object* v_ex_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_____do__lift_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Lean_Kernel_Exception_toMessageData(v_ex_527_, v_____do__lift_530_);
v___x_532_ = l_Lean_throwError___redArg(v_inst_528_, v_inst_529_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object* v_inst_533_, lean_object* v_toBind_534_, lean_object* v___f_535_, lean_object* v_____r_536_){
_start:
{
lean_object* v_getOptions_537_; lean_object* v___x_538_; 
v_getOptions_537_ = lean_ctor_get(v_inst_533_, 0);
lean_inc(v_getOptions_537_);
lean_dec_ref(v_inst_533_);
v___x_538_ = lean_apply_4(v_toBind_534_, lean_box(0), lean_box(0), v_getOptions_537_, v___f_535_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__2(lean_object* v___f_539_, lean_object* v_____r_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_apply_1(v___f_539_, v_____r_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_ex_545_){
_start:
{
lean_object* v_toBind_546_; lean_object* v___f_547_; lean_object* v___f_548_; 
v_toBind_546_ = lean_ctor_get(v_inst_542_, 1);
lean_inc_n(v_toBind_546_, 2);
lean_inc_ref(v_inst_543_);
lean_inc(v_ex_545_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__0), 4, 3);
lean_closure_set(v___f_547_, 0, v_ex_545_);
lean_closure_set(v___f_547_, 1, v_inst_542_);
lean_closure_set(v___f_547_, 2, v_inst_543_);
lean_inc_ref(v___f_547_);
lean_inc_ref(v_inst_544_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1), 4, 3);
lean_closure_set(v___f_548_, 0, v_inst_544_);
lean_closure_set(v___f_548_, 1, v_toBind_546_);
lean_closure_set(v___f_548_, 2, v___f_547_);
if (lean_obj_tag(v_ex_545_) == 16)
{
lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v___f_547_);
lean_dec_ref(v_inst_544_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__2), 2, 1);
lean_closure_set(v___f_549_, 0, v___f_548_);
v___x_550_ = l_Lean_throwInterruptException___redArg(v_inst_543_);
v___x_551_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_550_, v___f_549_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec_ref(v___f_548_);
lean_dec(v_ex_545_);
lean_dec_ref(v_inst_543_);
v___x_552_ = lean_box(0);
v___x_553_ = l_Lean_throwKernelException___redArg___lam__1(v_inst_544_, v_toBind_546_, v___f_547_, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object* v_m_554_, lean_object* v_00_u03b1_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_ex_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_throwKernelException___redArg(v_inst_556_, v_inst_557_, v_inst_558_, v_ex_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v_x_564_, 1);
v___x_566_ = l_Lean_throwKernelException___redArg(v_inst_561_, v_inst_562_, v_inst_563_, v_a_565_);
return v___x_566_;
}
else
{
lean_object* v_toApplicative_567_; lean_object* v_toPure_568_; lean_object* v_a_569_; lean_object* v___x_570_; 
v_toApplicative_567_ = lean_ctor_get(v_inst_561_, 0);
lean_inc_ref(v_toApplicative_567_);
lean_dec_ref(v_inst_563_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_inst_561_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_567_, 1);
lean_inc(v_toPure_568_);
lean_dec_ref(v_toApplicative_567_);
v_a_569_ = lean_ctor_get(v_x_564_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v_x_564_, 1);
v___x_570_ = lean_apply_2(v_toPure_568_, lean_box(0), v_a_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object* v_m_571_, lean_object* v_00_u03b1_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_x_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_ofExceptKernelException___redArg(v_inst_573_, v_inst_574_, v_inst_575_, v_x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object* v_inst_578_, lean_object* v_00_u03b1_579_, lean_object* v_d_580_, lean_object* v_x_581_, lean_object* v_ctx_582_){
_start:
{
lean_object* v_withRecDepth_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_withRecDepth_583_ = lean_ctor_get(v_inst_578_, 0);
lean_inc(v_withRecDepth_583_);
lean_dec_ref(v_inst_578_);
v___x_584_ = lean_apply_1(v_x_581_, v_ctx_582_);
v___x_585_ = lean_apply_3(v_withRecDepth_583_, lean_box(0), v_d_580_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object* v_inst_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_getRecDepth_588_; 
v_getRecDepth_588_ = lean_ctor_get(v_inst_586_, 1);
lean_inc(v_getRecDepth_588_);
return v_getRecDepth_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object* v_inst_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_589_, v_x_590_);
lean_dec(v_x_590_);
lean_dec_ref(v_inst_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object* v_inst_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_getMaxRecDepth_594_; 
v_getMaxRecDepth_594_ = lean_ctor_get(v_inst_592_, 2);
lean_inc(v_getMaxRecDepth_594_);
return v_getMaxRecDepth_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object* v_inst_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec_ref(v_inst_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object* v_inst_598_){
_start:
{
lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; 
lean_inc_ref_n(v_inst_598_, 2);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_599_, 0, v_inst_598_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_600_, 0, v_inst_598_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_601_, 0, v_inst_598_);
v___x_602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_602_, 0, v___f_599_);
lean_ctor_set(v___x_602_, 1, v___f_600_);
lean_ctor_set(v___x_602_, 2, v___f_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object* v_m_603_, lean_object* v_00_u03c1_604_, lean_object* v_inst_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(lean_object* v_inst_607_, lean_object* v_d_608_, lean_object* v_x_609_, lean_object* v_ctx_610_){
_start:
{
lean_object* v_withRecDepth_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_withRecDepth_611_ = lean_ctor_get(v_inst_607_, 0);
lean_inc(v_withRecDepth_611_);
lean_dec_ref(v_inst_607_);
lean_inc(v_ctx_610_);
v___x_612_ = lean_apply_1(v_x_609_, v_ctx_610_);
v___x_613_ = lean_apply_3(v_withRecDepth_611_, lean_box(0), v_d_608_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(lean_object* v_inst_614_, lean_object* v_d_615_, lean_object* v_x_616_, lean_object* v_ctx_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(v_inst_614_, v_d_615_, v_x_616_, v_ctx_617_);
lean_dec(v_ctx_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(lean_object* v_m_619_, lean_object* v_00_u03c9_620_, lean_object* v_00_u03c3_621_, lean_object* v_inst_622_, lean_object* v_00_u03b1_623_, lean_object* v_d_624_, lean_object* v_x_625_, lean_object* v_ctx_626_){
_start:
{
lean_object* v_withRecDepth_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_withRecDepth_627_ = lean_ctor_get(v_inst_622_, 0);
lean_inc(v_withRecDepth_627_);
lean_dec_ref(v_inst_622_);
lean_inc(v_ctx_626_);
v___x_628_ = lean_apply_1(v_x_625_, v_ctx_626_);
v___x_629_ = lean_apply_3(v_withRecDepth_627_, lean_box(0), v_d_624_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(lean_object* v_m_630_, lean_object* v_00_u03c9_631_, lean_object* v_00_u03c3_632_, lean_object* v_inst_633_, lean_object* v_00_u03b1_634_, lean_object* v_d_635_, lean_object* v_x_636_, lean_object* v_ctx_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(v_m_630_, v_00_u03c9_631_, v_00_u03c3_632_, v_inst_633_, v_00_u03b1_634_, v_d_635_, v_x_636_, v_ctx_637_);
lean_dec(v_ctx_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(lean_object* v_inst_639_){
_start:
{
lean_object* v_getRecDepth_640_; 
v_getRecDepth_640_ = lean_ctor_get(v_inst_639_, 1);
lean_inc(v_getRecDepth_640_);
return v_getRecDepth_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(lean_object* v_inst_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_641_);
lean_dec_ref(v_inst_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(lean_object* v_m_643_, lean_object* v_00_u03c9_644_, lean_object* v_00_u03c3_645_, lean_object* v_inst_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_getRecDepth_648_; 
v_getRecDepth_648_ = lean_ctor_get(v_inst_646_, 1);
lean_inc(v_getRecDepth_648_);
return v_getRecDepth_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(lean_object* v_m_649_, lean_object* v_00_u03c9_650_, lean_object* v_00_u03c3_651_, lean_object* v_inst_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(v_m_649_, v_00_u03c9_650_, v_00_u03c3_651_, v_inst_652_, v_x_653_);
lean_dec(v_x_653_);
lean_dec_ref(v_inst_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(lean_object* v_inst_655_){
_start:
{
lean_object* v_getMaxRecDepth_656_; 
v_getMaxRecDepth_656_ = lean_ctor_get(v_inst_655_, 2);
lean_inc(v_getMaxRecDepth_656_);
return v_getMaxRecDepth_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(lean_object* v_inst_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_657_);
lean_dec_ref(v_inst_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(lean_object* v_m_659_, lean_object* v_00_u03c9_660_, lean_object* v_00_u03c3_661_, lean_object* v_inst_662_, lean_object* v_x_663_){
_start:
{
lean_object* v_getMaxRecDepth_664_; 
v_getMaxRecDepth_664_ = lean_ctor_get(v_inst_662_, 2);
lean_inc(v_getMaxRecDepth_664_);
return v_getMaxRecDepth_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(lean_object* v_m_665_, lean_object* v_00_u03c9_666_, lean_object* v_00_u03c3_667_, lean_object* v_inst_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(v_m_665_, v_00_u03c9_666_, v_00_u03c3_667_, v_inst_668_, v_x_669_);
lean_dec(v_x_669_);
lean_dec_ref(v_inst_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object* v_inst_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_inc_ref_n(v_inst_671_, 2);
v___x_672_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed), 8, 4);
lean_closure_set(v___x_672_, 0, lean_box(0));
lean_closure_set(v___x_672_, 1, lean_box(0));
lean_closure_set(v___x_672_, 2, lean_box(0));
lean_closure_set(v___x_672_, 3, v_inst_671_);
v___x_673_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed), 5, 4);
lean_closure_set(v___x_673_, 0, lean_box(0));
lean_closure_set(v___x_673_, 1, lean_box(0));
lean_closure_set(v___x_673_, 2, lean_box(0));
lean_closure_set(v___x_673_, 3, v_inst_671_);
v___x_674_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed), 5, 4);
lean_closure_set(v___x_674_, 0, lean_box(0));
lean_closure_set(v___x_674_, 1, lean_box(0));
lean_closure_set(v___x_674_, 2, lean_box(0));
lean_closure_set(v___x_674_, 3, v_inst_671_);
v___x_675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_675_, 0, v___x_672_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object* v_m_676_, lean_object* v_00_u03c9_677_, lean_object* v_00_u03c3_678_, lean_object* v_inst_679_, lean_object* v_inst_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object* v_m_682_, lean_object* v_00_u03c9_683_, lean_object* v_00_u03c3_684_, lean_object* v_inst_685_, lean_object* v_inst_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(v_m_682_, v_00_u03c9_683_, v_00_u03c3_684_, v_inst_685_, v_inst_686_);
lean_dec_ref(v_inst_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(lean_object* v_inst_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_withRecDepth_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_withRecDepth_692_ = lean_ctor_get(v_inst_688_, 0);
lean_inc(v_withRecDepth_692_);
lean_dec_ref(v_inst_688_);
lean_inc(v_a_691_);
v___x_693_ = lean_apply_1(v_a_690_, v_a_691_);
v___x_694_ = lean_apply_3(v_withRecDepth_692_, lean_box(0), v_a_689_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(lean_object* v_inst_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(v_inst_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(lean_object* v_00_u03b1_700_, lean_object* v_m_701_, lean_object* v_00_u03c9_702_, lean_object* v_00_u03b2_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_00_u03b1_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_withRecDepth_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_withRecDepth_712_ = lean_ctor_get(v_inst_707_, 0);
lean_inc(v_withRecDepth_712_);
lean_dec_ref(v_inst_707_);
lean_inc(v_a_711_);
v___x_713_ = lean_apply_1(v_a_710_, v_a_711_);
v___x_714_ = lean_apply_3(v_withRecDepth_712_, lean_box(0), v_a_709_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(lean_object* v_00_u03b1_715_, lean_object* v_m_716_, lean_object* v_00_u03c9_717_, lean_object* v_00_u03b2_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_00_u03b1_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(v_00_u03b1_715_, v_m_716_, v_00_u03c9_717_, v_00_u03b2_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_inst_722_, v_00_u03b1_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_inst_720_);
lean_dec_ref(v_inst_719_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(lean_object* v_inst_728_){
_start:
{
lean_object* v_getRecDepth_729_; 
v_getRecDepth_729_ = lean_ctor_get(v_inst_728_, 1);
lean_inc(v_getRecDepth_729_);
return v_getRecDepth_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(lean_object* v_inst_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_730_);
lean_dec_ref(v_inst_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(lean_object* v_00_u03b1_732_, lean_object* v_m_733_, lean_object* v_00_u03c9_734_, lean_object* v_00_u03b2_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_getRecDepth_741_; 
v_getRecDepth_741_ = lean_ctor_get(v_inst_739_, 1);
lean_inc(v_getRecDepth_741_);
return v_getRecDepth_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(lean_object* v_00_u03b1_742_, lean_object* v_m_743_, lean_object* v_00_u03c9_744_, lean_object* v_00_u03b2_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(v_00_u03b1_742_, v_m_743_, v_00_u03c9_744_, v_00_u03b2_745_, v_inst_746_, v_inst_747_, v_inst_748_, v_inst_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_inst_749_);
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(lean_object* v_inst_752_){
_start:
{
lean_object* v_getMaxRecDepth_753_; 
v_getMaxRecDepth_753_ = lean_ctor_get(v_inst_752_, 2);
lean_inc(v_getMaxRecDepth_753_);
return v_getMaxRecDepth_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(lean_object* v_inst_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_754_);
lean_dec_ref(v_inst_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(lean_object* v_00_u03b1_756_, lean_object* v_m_757_, lean_object* v_00_u03c9_758_, lean_object* v_00_u03b2_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_getMaxRecDepth_765_; 
v_getMaxRecDepth_765_ = lean_ctor_get(v_inst_763_, 2);
lean_inc(v_getMaxRecDepth_765_);
return v_getMaxRecDepth_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(lean_object* v_00_u03b1_766_, lean_object* v_m_767_, lean_object* v_00_u03c9_768_, lean_object* v_00_u03b2_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(v_00_u03b1_766_, v_m_767_, v_00_u03c9_768_, v_00_u03b2_769_, v_inst_770_, v_inst_771_, v_inst_772_, v_inst_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_inst_773_);
lean_dec_ref(v_inst_771_);
lean_dec_ref(v_inst_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_inc_ref_n(v_inst_779_, 2);
lean_inc_ref_n(v_inst_777_, 2);
lean_inc_ref_n(v_inst_776_, 2);
v___x_780_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed), 12, 8);
lean_closure_set(v___x_780_, 0, lean_box(0));
lean_closure_set(v___x_780_, 1, lean_box(0));
lean_closure_set(v___x_780_, 2, lean_box(0));
lean_closure_set(v___x_780_, 3, lean_box(0));
lean_closure_set(v___x_780_, 4, v_inst_776_);
lean_closure_set(v___x_780_, 5, v_inst_777_);
lean_closure_set(v___x_780_, 6, v_inst_778_);
lean_closure_set(v___x_780_, 7, v_inst_779_);
v___x_781_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed), 9, 8);
lean_closure_set(v___x_781_, 0, lean_box(0));
lean_closure_set(v___x_781_, 1, lean_box(0));
lean_closure_set(v___x_781_, 2, lean_box(0));
lean_closure_set(v___x_781_, 3, lean_box(0));
lean_closure_set(v___x_781_, 4, v_inst_776_);
lean_closure_set(v___x_781_, 5, v_inst_777_);
lean_closure_set(v___x_781_, 6, v_inst_778_);
lean_closure_set(v___x_781_, 7, v_inst_779_);
v___x_782_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed), 9, 8);
lean_closure_set(v___x_782_, 0, lean_box(0));
lean_closure_set(v___x_782_, 1, lean_box(0));
lean_closure_set(v___x_782_, 2, lean_box(0));
lean_closure_set(v___x_782_, 3, lean_box(0));
lean_closure_set(v___x_782_, 4, v_inst_776_);
lean_closure_set(v___x_782_, 5, v_inst_777_);
lean_closure_set(v___x_782_, 6, v_inst_778_);
lean_closure_set(v___x_782_, 7, v_inst_779_);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object* v_00_u03b1_784_, lean_object* v_m_785_, lean_object* v_00_u03c9_786_, lean_object* v_00_u03b2_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(v_inst_788_, v_inst_789_, v_inst_791_, v_inst_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object* v_00_u03b1_794_, lean_object* v_m_795_, lean_object* v_00_u03c9_796_, lean_object* v_00_u03b2_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_inst_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad(v_00_u03b1_794_, v_m_795_, v_00_u03c9_796_, v_00_u03b2_797_, v_inst_798_, v_inst_799_, v_inst_800_, v_inst_801_, v_inst_802_);
lean_dec_ref(v_inst_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0(lean_object* v_withRecDepth_804_, lean_object* v_00_u03b1_805_, lean_object* v_d_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = lean_apply_3(v_withRecDepth_804_, lean_box(0), v_d_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1(lean_object* v_toPure_809_, lean_object* v_____do__lift_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v_____do__lift_810_);
v___x_812_ = lean_apply_2(v_toPure_809_, lean_box(0), v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v_toApplicative_815_; lean_object* v_withRecDepth_816_; lean_object* v_getRecDepth_817_; lean_object* v_getMaxRecDepth_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_831_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_813_, 0);
lean_inc_ref(v_toApplicative_815_);
v_withRecDepth_816_ = lean_ctor_get(v_inst_814_, 0);
v_getRecDepth_817_ = lean_ctor_get(v_inst_814_, 1);
v_getMaxRecDepth_818_ = lean_ctor_get(v_inst_814_, 2);
v_isSharedCheck_831_ = !lean_is_exclusive(v_inst_814_);
if (v_isSharedCheck_831_ == 0)
{
v___x_820_ = v_inst_814_;
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_getMaxRecDepth_818_);
lean_inc(v_getRecDepth_817_);
lean_inc(v_withRecDepth_816_);
lean_dec(v_inst_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_toBind_822_; lean_object* v_toPure_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v_toBind_822_ = lean_ctor_get(v_inst_813_, 1);
lean_inc_n(v_toBind_822_, 2);
lean_dec_ref(v_inst_813_);
v_toPure_823_ = lean_ctor_get(v_toApplicative_815_, 1);
lean_inc(v_toPure_823_);
lean_dec_ref(v_toApplicative_815_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_824_, 0, v_withRecDepth_816_);
v___f_825_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_825_, 0, v_toPure_823_);
lean_inc_ref(v___f_825_);
v___x_826_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v_getRecDepth_817_, v___f_825_);
v___x_827_ = lean_apply_4(v_toBind_822_, lean_box(0), lean_box(0), v_getMaxRecDepth_818_, v___f_825_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 2, v___x_827_);
lean_ctor_set(v___x_820_, 1, v___x_826_);
lean_ctor_set(v___x_820_, 0, v___f_824_);
v___x_829_ = v___x_820_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___f_824_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad(lean_object* v_m_832_, lean_object* v_inst_833_, lean_object* v_inst_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_instMonadRecDepthOptionTOfMonad___redArg(v_inst_833_, v_inst_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l_Lean_maxRecDepthErrorMessage;
v___x_842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3);
v___x_844_ = l_Lean_MessageData_ofFormat(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4);
v___x_846_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_847_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object* v_inst_848_, lean_object* v_ref_849_){
_start:
{
lean_object* v_toMonadExceptOf_850_; lean_object* v_throw_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_860_; 
v_toMonadExceptOf_850_ = lean_ctor_get(v_inst_848_, 0);
lean_inc_ref(v_toMonadExceptOf_850_);
lean_dec_ref(v_inst_848_);
v_throw_851_ = lean_ctor_get(v_toMonadExceptOf_850_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_toMonadExceptOf_850_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_toMonadExceptOf_850_, 1);
lean_dec(v_unused_861_);
v___x_853_ = v_toMonadExceptOf_850_;
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_throw_851_);
lean_dec(v_toMonadExceptOf_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_855_);
lean_ctor_set(v___x_853_, 0, v_ref_849_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_ref_849_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_apply_2(v_throw_851_, lean_box(0), v___x_857_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object* v_m_862_, lean_object* v_00_u03b1_863_, lean_object* v_inst_864_, lean_object* v_ref_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_864_, v_ref_865_);
return v___x_866_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object* v_ex_867_){
_start:
{
if (lean_obj_tag(v_ex_867_) == 0)
{
lean_object* v_msg_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_msg_868_ = lean_ctor_get(v_ex_867_, 1);
lean_inc_ref(v_msg_868_);
lean_dec_ref_known(v_ex_867_, 2);
v___x_869_ = l_Lean_MessageData_stripNestedTags(v_msg_868_);
v___x_870_ = l_Lean_MessageData_kind(v___x_869_);
lean_dec_ref(v___x_869_);
v___x_871_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_872_ = lean_name_eq(v___x_870_, v___x_871_);
lean_dec(v___x_870_);
return v___x_872_;
}
else
{
uint8_t v___x_873_; 
lean_dec_ref(v_ex_867_);
v___x_873_ = 0;
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object* v_ex_874_){
_start:
{
uint8_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l_Lean_Exception_isMaxRecDepth(v_ex_874_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object* v_inst_877_, lean_object* v_____do__lift_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_877_, v_____do__lift_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object* v_curr_880_, lean_object* v_withRecDepth_881_, lean_object* v_x_882_, lean_object* v_toMonadRef_883_, lean_object* v_toBind_884_, lean_object* v___f_885_, lean_object* v_max_886_){
_start:
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_nat_dec_eq(v_max_886_, v___x_891_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = lean_nat_dec_eq(v_curr_880_, v_max_886_);
if (v___x_893_ == 0)
{
lean_dec(v___f_885_);
lean_dec(v_toBind_884_);
lean_dec_ref(v_toMonadRef_883_);
goto v___jp_887_;
}
else
{
lean_object* v_getRef_894_; lean_object* v___x_895_; 
lean_dec(v_x_882_);
lean_dec(v_withRecDepth_881_);
v_getRef_894_ = lean_ctor_get(v_toMonadRef_883_, 0);
lean_inc(v_getRef_894_);
lean_dec_ref(v_toMonadRef_883_);
v___x_895_ = lean_apply_4(v_toBind_884_, lean_box(0), lean_box(0), v_getRef_894_, v___f_885_);
return v___x_895_;
}
}
else
{
lean_dec(v___f_885_);
lean_dec(v_toBind_884_);
lean_dec_ref(v_toMonadRef_883_);
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_curr_880_, v___x_888_);
v___x_890_ = lean_apply_3(v_withRecDepth_881_, lean_box(0), v___x_889_, v_x_882_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object* v_curr_896_, lean_object* v_withRecDepth_897_, lean_object* v_x_898_, lean_object* v_toMonadRef_899_, lean_object* v_toBind_900_, lean_object* v___f_901_, lean_object* v_max_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_withIncRecDepth___redArg___lam__1(v_curr_896_, v_withRecDepth_897_, v_x_898_, v_toMonadRef_899_, v_toBind_900_, v___f_901_, v_max_902_);
lean_dec(v_max_902_);
lean_dec(v_curr_896_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object* v_withRecDepth_904_, lean_object* v_x_905_, lean_object* v_toMonadRef_906_, lean_object* v_toBind_907_, lean_object* v___f_908_, lean_object* v_getMaxRecDepth_909_, lean_object* v_curr_910_){
_start:
{
lean_object* v___f_911_; lean_object* v___x_912_; 
lean_inc(v_toBind_907_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_911_, 0, v_curr_910_);
lean_closure_set(v___f_911_, 1, v_withRecDepth_904_);
lean_closure_set(v___f_911_, 2, v_x_905_);
lean_closure_set(v___f_911_, 3, v_toMonadRef_906_);
lean_closure_set(v___f_911_, 4, v_toBind_907_);
lean_closure_set(v___f_911_, 5, v___f_908_);
v___x_912_ = lean_apply_4(v_toBind_907_, lean_box(0), lean_box(0), v_getMaxRecDepth_909_, v___f_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_toBind_917_; lean_object* v_withRecDepth_918_; lean_object* v_getRecDepth_919_; lean_object* v_getMaxRecDepth_920_; lean_object* v_toMonadRef_921_; lean_object* v___f_922_; lean_object* v___f_923_; lean_object* v___x_924_; 
v_toBind_917_ = lean_ctor_get(v_inst_913_, 1);
lean_inc_n(v_toBind_917_, 2);
lean_dec_ref(v_inst_913_);
v_withRecDepth_918_ = lean_ctor_get(v_inst_915_, 0);
lean_inc(v_withRecDepth_918_);
v_getRecDepth_919_ = lean_ctor_get(v_inst_915_, 1);
lean_inc(v_getRecDepth_919_);
v_getMaxRecDepth_920_ = lean_ctor_get(v_inst_915_, 2);
lean_inc(v_getMaxRecDepth_920_);
lean_dec_ref(v_inst_915_);
v_toMonadRef_921_ = lean_ctor_get(v_inst_914_, 1);
lean_inc_ref(v_toMonadRef_921_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_922_, 0, v_inst_914_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_923_, 0, v_withRecDepth_918_);
lean_closure_set(v___f_923_, 1, v_x_916_);
lean_closure_set(v___f_923_, 2, v_toMonadRef_921_);
lean_closure_set(v___f_923_, 3, v_toBind_917_);
lean_closure_set(v___f_923_, 4, v___f_922_);
lean_closure_set(v___f_923_, 5, v_getMaxRecDepth_920_);
v___x_924_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v_getRecDepth_919_, v___f_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object* v_m_925_, lean_object* v_00_u03b1_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_x_930_){
_start:
{
lean_object* v_toBind_931_; lean_object* v_withRecDepth_932_; lean_object* v_getRecDepth_933_; lean_object* v_getMaxRecDepth_934_; lean_object* v_toMonadRef_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___x_938_; 
v_toBind_931_ = lean_ctor_get(v_inst_927_, 1);
lean_inc_n(v_toBind_931_, 2);
lean_dec_ref(v_inst_927_);
v_withRecDepth_932_ = lean_ctor_get(v_inst_929_, 0);
lean_inc(v_withRecDepth_932_);
v_getRecDepth_933_ = lean_ctor_get(v_inst_929_, 1);
lean_inc(v_getRecDepth_933_);
v_getMaxRecDepth_934_ = lean_ctor_get(v_inst_929_, 2);
lean_inc(v_getMaxRecDepth_934_);
lean_dec_ref(v_inst_929_);
v_toMonadRef_935_ = lean_ctor_get(v_inst_928_, 1);
lean_inc_ref(v_toMonadRef_935_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_936_, 0, v_inst_928_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_937_, 0, v_withRecDepth_932_);
lean_closure_set(v___f_937_, 1, v_x_930_);
lean_closure_set(v___f_937_, 2, v_toMonadRef_935_);
lean_closure_set(v___f_937_, 3, v_toBind_931_);
lean_closure_set(v___f_937_, 4, v___f_936_);
lean_closure_set(v___f_937_, 5, v_getMaxRecDepth_934_);
v___x_938_ = lean_apply_4(v_toBind_931_, lean_box(0), lean_box(0), v_getRecDepth_933_, v___f_937_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6));
v___x_1023_ = l_String_toRawSubstring_x27(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23));
v___x_1060_ = l_String_toRawSubstring_x27(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object* v_x_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_termThrowError_____00__closed__2));
lean_inc(v_x_1074_);
v___x_1078_ = l_Lean_Syntax_isOfKind(v_x_1074_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec(v_x_1074_);
v___x_1079_ = lean_box(1);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_a_1076_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = l_Lean_Syntax_getArg(v_x_1074_, v___x_1081_);
lean_dec(v_x_1074_);
v___x_1083_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1082_);
v___x_1084_ = l_Lean_Syntax_isOfKind(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v_quotContext_1085_; lean_object* v_currMacroScope_1086_; lean_object* v_ref_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_quotContext_1085_ = lean_ctor_get(v_a_1075_, 1);
v_currMacroScope_1086_ = lean_ctor_get(v_a_1075_, 2);
v_ref_1087_ = lean_ctor_get(v_a_1075_, 5);
v___x_1088_ = l_Lean_SourceInfo_fromRef(v_ref_1087_, v___x_1084_);
v___x_1089_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1090_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1091_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc(v_currMacroScope_1086_);
lean_inc(v_quotContext_1085_);
v___x_1092_ = l_Lean_addMacroScope(v_quotContext_1085_, v___x_1091_, v_currMacroScope_1086_);
v___x_1093_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1088_, 2);
v___x_1094_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1088_);
lean_ctor_set(v___x_1094_, 1, v___x_1090_);
lean_ctor_set(v___x_1094_, 2, v___x_1092_);
lean_ctor_set(v___x_1094_, 3, v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1096_ = l_Lean_Syntax_node1(v___x_1088_, v___x_1095_, v___x_1082_);
v___x_1097_ = l_Lean_Syntax_node2(v___x_1088_, v___x_1089_, v___x_1094_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1076_);
return v___x_1098_;
}
else
{
lean_object* v_quotContext_1099_; lean_object* v_currMacroScope_1100_; lean_object* v_ref_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_quotContext_1099_ = lean_ctor_get(v_a_1075_, 1);
v_currMacroScope_1100_ = lean_ctor_get(v_a_1075_, 2);
v_ref_1101_ = lean_ctor_get(v_a_1075_, 5);
v___x_1102_ = 0;
v___x_1103_ = l_Lean_SourceInfo_fromRef(v_ref_1101_, v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1105_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1106_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc_n(v_currMacroScope_1100_, 2);
lean_inc_n(v_quotContext_1099_, 2);
v___x_1107_ = l_Lean_addMacroScope(v_quotContext_1099_, v___x_1106_, v_currMacroScope_1100_);
v___x_1108_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1103_, 10);
v___x_1109_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1103_);
lean_ctor_set(v___x_1109_, 1, v___x_1105_);
lean_ctor_set(v___x_1109_, 2, v___x_1107_);
lean_ctor_set(v___x_1109_, 3, v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1111_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1112_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1113_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1103_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1116_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Lean_addMacroScope(v_quotContext_1099_, v___x_1117_, v_currMacroScope_1100_);
v___x_1119_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1103_);
lean_ctor_set(v___x_1120_, 1, v___x_1116_);
lean_ctor_set(v___x_1120_, 2, v___x_1118_);
lean_ctor_set(v___x_1120_, 3, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node1(v___x_1103_, v___x_1115_, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node2(v___x_1103_, v___x_1112_, v___x_1114_, v___x_1121_);
v___x_1123_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1124_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1103_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_Syntax_node2(v___x_1103_, v___x_1123_, v___x_1125_, v___x_1082_);
v___x_1127_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1103_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node3(v___x_1103_, v___x_1111_, v___x_1122_, v___x_1126_, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node1(v___x_1103_, v___x_1110_, v___x_1129_);
v___x_1131_ = l_Lean_Syntax_node2(v___x_1103_, v___x_1104_, v___x_1109_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_a_1076_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(lean_object* v_x_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(v_x_1133_, v_a_1134_, v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1136_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0));
v___x_1139_ = l_String_toRawSubstring_x27(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object* v_x_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_termThrowErrorAt_________00__closed__1));
lean_inc(v_x_1150_);
v___x_1154_ = l_Lean_Syntax_isOfKind(v_x_1150_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_x_1150_);
v___x_1155_ = lean_box(1);
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v_a_1152_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = l_Lean_Syntax_getArg(v_x_1150_, v___x_1157_);
v___x_1159_ = lean_unsigned_to_nat(2u);
v___x_1160_ = l_Lean_Syntax_getArg(v_x_1150_, v___x_1159_);
lean_dec(v_x_1150_);
v___x_1161_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1160_);
v___x_1162_ = l_Lean_Syntax_isOfKind(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v_quotContext_1163_; lean_object* v_currMacroScope_1164_; lean_object* v_ref_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_quotContext_1163_ = lean_ctor_get(v_a_1151_, 1);
v_currMacroScope_1164_ = lean_ctor_get(v_a_1151_, 2);
v_ref_1165_ = lean_ctor_get(v_a_1151_, 5);
v___x_1166_ = l_Lean_SourceInfo_fromRef(v_ref_1165_, v___x_1162_);
v___x_1167_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1168_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1169_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc(v_currMacroScope_1164_);
lean_inc(v_quotContext_1163_);
v___x_1170_ = l_Lean_addMacroScope(v_quotContext_1163_, v___x_1169_, v_currMacroScope_1164_);
v___x_1171_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1166_, 2);
v___x_1172_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1166_);
lean_ctor_set(v___x_1172_, 1, v___x_1168_);
lean_ctor_set(v___x_1172_, 2, v___x_1170_);
lean_ctor_set(v___x_1172_, 3, v___x_1171_);
v___x_1173_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1174_ = l_Lean_Syntax_node2(v___x_1166_, v___x_1173_, v___x_1158_, v___x_1160_);
v___x_1175_ = l_Lean_Syntax_node2(v___x_1166_, v___x_1167_, v___x_1172_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_a_1152_);
return v___x_1176_;
}
else
{
lean_object* v_quotContext_1177_; lean_object* v_currMacroScope_1178_; lean_object* v_ref_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_quotContext_1177_ = lean_ctor_get(v_a_1151_, 1);
v_currMacroScope_1178_ = lean_ctor_get(v_a_1151_, 2);
v_ref_1179_ = lean_ctor_get(v_a_1151_, 5);
v___x_1180_ = 0;
v___x_1181_ = l_Lean_SourceInfo_fromRef(v_ref_1179_, v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1183_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1184_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc_n(v_currMacroScope_1178_, 2);
lean_inc_n(v_quotContext_1177_, 2);
v___x_1185_ = l_Lean_addMacroScope(v_quotContext_1177_, v___x_1184_, v_currMacroScope_1178_);
v___x_1186_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1181_, 10);
v___x_1187_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1181_);
lean_ctor_set(v___x_1187_, 1, v___x_1183_);
lean_ctor_set(v___x_1187_, 2, v___x_1185_);
lean_ctor_set(v___x_1187_, 3, v___x_1186_);
v___x_1188_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1189_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1190_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1191_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1181_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1194_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1195_ = lean_box(0);
v___x_1196_ = l_Lean_addMacroScope(v_quotContext_1177_, v___x_1195_, v_currMacroScope_1178_);
v___x_1197_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1181_);
lean_ctor_set(v___x_1198_, 1, v___x_1194_);
lean_ctor_set(v___x_1198_, 2, v___x_1196_);
lean_ctor_set(v___x_1198_, 3, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_node1(v___x_1181_, v___x_1193_, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node2(v___x_1181_, v___x_1190_, v___x_1192_, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1202_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1181_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_Syntax_node2(v___x_1181_, v___x_1201_, v___x_1203_, v___x_1160_);
v___x_1205_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1181_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_Syntax_node3(v___x_1181_, v___x_1189_, v___x_1200_, v___x_1204_, v___x_1206_);
v___x_1208_ = l_Lean_Syntax_node2(v___x_1181_, v___x_1188_, v___x_1158_, v___x_1207_);
v___x_1209_ = l_Lean_Syntax_node2(v___x_1181_, v___x_1182_, v___x_1187_, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v_a_1152_);
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(lean_object* v_x_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(v_x_1211_, v_a_1212_, v_a_1213_);
lean_dec_ref(v_a_1212_);
return v_res_1214_;
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
