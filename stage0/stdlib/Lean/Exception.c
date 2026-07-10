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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx___boxed(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Exception_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_ref_8_; lean_object* v_msg_9_; lean_object* v___x_10_; 
v_ref_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_ref_8_);
v_msg_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_msg_9_);
lean_dec_ref_known(v_t_6_, 2);
v___x_10_ = lean_apply_2(v_k_7_, v_ref_8_, v_msg_9_);
return v___x_10_;
}
else
{
lean_object* v_id_11_; lean_object* v_extra_12_; lean_object* v___x_13_; 
v_id_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_id_11_);
v_extra_12_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_extra_12_);
lean_dec_ref_known(v_t_6_, 2);
v___x_13_ = lean_apply_2(v_k_7_, v_id_11_, v_extra_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Exception_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Exception_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_error_elim___redArg(lean_object* v_t_26_, lean_object* v_error_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Exception_ctorElim___redArg(v_t_26_, v_error_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_error_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_error_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Exception_ctorElim___redArg(v_t_30_, v_error_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_internal_elim___redArg(lean_object* v_t_34_, lean_object* v_internal_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Exception_ctorElim___redArg(v_t_34_, v_internal_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_internal_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_internal_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Exception_ctorElim___redArg(v_t_38_, v_internal_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_toMessageData(lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_msg_43_; 
v_msg_43_ = lean_ctor_get(v_x_42_, 1);
lean_inc_ref(v_msg_43_);
lean_dec_ref_known(v_x_42_, 2);
return v_msg_43_;
}
else
{
lean_object* v_id_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_id_44_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_id_44_);
lean_dec_ref_known(v_x_42_, 2);
v___x_45_ = l_Lean_InternalExceptionId_toString(v_id_44_);
v___x_46_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
v___x_47_ = l_Lean_MessageData_ofFormat(v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v_msg_49_; uint8_t v___x_50_; 
v_msg_49_ = lean_ctor_get(v_x_48_, 1);
lean_inc_ref(v_msg_49_);
lean_dec_ref_known(v_x_48_, 2);
v___x_50_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_49_);
return v___x_50_;
}
else
{
uint8_t v___x_51_; 
lean_dec_ref(v_x_48_);
v___x_51_ = 0;
return v___x_51_;
}
}
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
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_alloc_ctor(0, 10, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object* v_toPure_253_, lean_object* v_msg_254_, lean_object* v_declHint_255_, lean_object* v_env_256_){
_start:
{
uint8_t v___y_258_; uint8_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = l_Lean_Name_isAnonymous(v_declHint_255_);
v___x_307_ = lean_bool_not(v___x_306_);
if (v___x_307_ == 0)
{
v___y_258_ = v___x_307_;
goto v___jp_257_;
}
else
{
uint8_t v_isExporting_308_; 
v_isExporting_308_ = lean_ctor_get_uint8(v_env_256_, sizeof(void*)*8);
v___y_258_ = v_isExporting_308_;
goto v___jp_257_;
}
v___jp_257_:
{
if (v___y_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_255_);
v___x_259_ = lean_apply_2(v_toPure_253_, lean_box(0), v_msg_254_);
return v___x_259_;
}
else
{
uint8_t v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = 0;
lean_inc_ref(v_env_256_);
v___x_261_ = l_Lean_Environment_setExporting(v_env_256_, v___x_260_);
lean_inc(v_declHint_255_);
lean_inc_ref(v___x_261_);
v___x_262_ = l_Lean_Environment_contains(v___x_261_, v_declHint_255_, v___y_258_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec_ref(v___x_261_);
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_255_);
v___x_263_ = lean_apply_2(v_toPure_253_, lean_box(0), v_msg_254_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_c_269_; lean_object* v___x_270_; 
v___x_264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2);
v___x_265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5);
v___x_266_ = l_Lean_Options_empty;
v___x_267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_267_, 0, v___x_261_);
lean_ctor_set(v___x_267_, 1, v___x_264_);
lean_ctor_set(v___x_267_, 2, v___x_265_);
lean_ctor_set(v___x_267_, 3, v___x_266_);
lean_inc(v_declHint_255_);
v___x_268_ = l_Lean_MessageData_ofConstName(v_declHint_255_, v___x_260_);
v_c_269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_269_, 0, v___x_267_);
lean_ctor_set(v_c_269_, 1, v___x_268_);
v___x_270_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_256_, v_declHint_255_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_255_);
v___x_271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_c_269_);
v___x_273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_MessageData_note(v___x_274_);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v_msg_254_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_apply_2(v_toPure_253_, lean_box(0), v___x_276_);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_mod_282_; uint8_t v___x_283_; 
v_val_278_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_270_, 1);
v___x_279_ = lean_box(0);
v___x_280_ = l_Lean_Environment_header(v_env_256_);
lean_dec_ref(v_env_256_);
v___x_281_ = l_Lean_EnvironmentHeader_moduleNames(v___x_280_);
v_mod_282_ = lean_array_get(v___x_279_, v___x_281_, v_val_278_);
lean_dec(v_val_278_);
lean_dec_ref(v___x_281_);
v___x_283_ = l_Lean_isPrivateName(v_declHint_255_);
lean_dec(v_declHint_255_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v_c_269_);
v___x_286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_MessageData_ofName(v_mod_282_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_MessageData_note(v___x_291_);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v_msg_254_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_apply_2(v_toPure_253_, lean_box(0), v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_c_269_);
v___x_297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_MessageData_ofName(v_mod_282_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_MessageData_note(v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v_msg_254_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_apply_2(v_toPure_253_, lean_box(0), v___x_304_);
return v___x_305_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg(lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_msg_311_, lean_object* v_declHint_312_){
_start:
{
lean_object* v_toApplicative_313_; lean_object* v_toBind_314_; lean_object* v_getEnv_315_; lean_object* v_toPure_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v_toApplicative_313_ = lean_ctor_get(v_inst_309_, 0);
lean_inc_ref(v_toApplicative_313_);
v_toBind_314_ = lean_ctor_get(v_inst_309_, 1);
lean_inc(v_toBind_314_);
lean_dec_ref(v_inst_309_);
v_getEnv_315_ = lean_ctor_get(v_inst_310_, 0);
lean_inc(v_getEnv_315_);
lean_dec_ref(v_inst_310_);
v_toPure_316_ = lean_ctor_get(v_toApplicative_313_, 1);
lean_inc(v_toPure_316_);
lean_dec_ref(v_toApplicative_313_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_317_, 0, v_toPure_316_);
lean_closure_set(v___f_317_, 1, v_msg_311_);
lean_closure_set(v___f_317_, 2, v_declHint_312_);
v___x_318_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v_getEnv_315_, v___f_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore(lean_object* v_m_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_msg_323_, lean_object* v_declHint_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_320_, v_inst_321_, v_msg_323_, v_declHint_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___boxed(lean_object* v_m_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_msg_330_, lean_object* v_declHint_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_mkUnknownIdentifierMessageCore(v_m_326_, v_inst_327_, v_inst_328_, v_inst_329_, v_msg_330_, v_declHint_331_);
lean_dec_ref(v_inst_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(lean_object* v_toPure_333_, lean_object* v_msg_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Lean_unknownIdentifierMessageTag;
v___x_336_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_msg_334_);
v___x_337_ = lean_apply_2(v_toPure_333_, lean_box(0), v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg(lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_msg_340_, lean_object* v_declHint_341_){
_start:
{
lean_object* v_toApplicative_342_; lean_object* v_toBind_343_; lean_object* v_toPure_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_toApplicative_342_ = lean_ctor_get(v_inst_338_, 0);
v_toBind_343_ = lean_ctor_get(v_inst_338_, 1);
lean_inc(v_toBind_343_);
v_toPure_344_ = lean_ctor_get(v_toApplicative_342_, 1);
lean_inc(v_toPure_344_);
v___x_345_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_338_, v_inst_339_, v_msg_340_, v_declHint_341_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_346_, 0, v_toPure_344_);
v___x_347_ = lean_apply_4(v_toBind_343_, lean_box(0), lean_box(0), v___x_345_, v___f_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object* v_m_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_msg_352_, lean_object* v_declHint_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_349_, v_inst_350_, v_msg_352_, v_declHint_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___boxed(lean_object* v_m_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_msg_359_, lean_object* v_declHint_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_mkUnknownIdentifierMessage(v_m_355_, v_inst_356_, v_inst_357_, v_inst_358_, v_msg_359_, v_declHint_360_);
lean_dec_ref(v_inst_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg___lam__0(lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_ref_364_, lean_object* v_____do__lift_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_throwErrorAt___redArg(v_inst_362_, v_inst_363_, v_ref_364_, v_____do__lift_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_ref_370_, lean_object* v_msg_371_, lean_object* v_declHint_372_){
_start:
{
lean_object* v_toBind_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_toBind_373_ = lean_ctor_get(v_inst_367_, 1);
lean_inc(v_toBind_373_);
lean_inc_ref(v_inst_367_);
v___f_374_ = lean_alloc_closure((void*)(l_Lean_throwUnknownIdentifierAt___redArg___lam__0), 4, 3);
lean_closure_set(v___f_374_, 0, v_inst_367_);
lean_closure_set(v___f_374_, 1, v_inst_369_);
lean_closure_set(v___f_374_, 2, v_ref_370_);
v___x_375_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_367_, v_inst_368_, v_msg_371_, v_declHint_372_);
v___x_376_ = lean_apply_4(v_toBind_373_, lean_box(0), lean_box(0), v___x_375_, v___f_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object* v_m_377_, lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_ref_382_, lean_object* v_msg_383_, lean_object* v_declHint_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_379_, v_inst_380_, v_inst_381_, v_ref_382_, v_msg_383_, v_declHint_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__0));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__2));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_ref_395_, lean_object* v_constName_396_){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_397_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__1, &l_Lean_throwUnknownConstantAt___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__1);
v___x_398_ = 0;
lean_inc(v_constName_396_);
v___x_399_ = l_Lean_MessageData_ofConstName(v_constName_396_, v___x_398_);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_397_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__3, &l_Lean_throwUnknownConstantAt___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__3);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_392_, v_inst_393_, v_inst_394_, v_ref_395_, v___x_402_, v_constName_396_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object* v_m_404_, lean_object* v_00_u03b1_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_ref_409_, lean_object* v_constName_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_406_, v_inst_407_, v_inst_408_, v_ref_409_, v_constName_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_constName_415_, lean_object* v_____do__lift_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_412_, v_inst_413_, v_inst_414_, v_____do__lift_416_, v_constName_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_constName_421_){
_start:
{
lean_object* v_toMonadRef_422_; lean_object* v_toBind_423_; lean_object* v_getRef_424_; lean_object* v___f_425_; lean_object* v___x_426_; 
v_toMonadRef_422_ = lean_ctor_get(v_inst_420_, 1);
v_toBind_423_ = lean_ctor_get(v_inst_418_, 1);
lean_inc(v_toBind_423_);
v_getRef_424_ = lean_ctor_get(v_toMonadRef_422_, 0);
lean_inc(v_getRef_424_);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___redArg___lam__0), 5, 4);
lean_closure_set(v___f_425_, 0, v_inst_418_);
lean_closure_set(v___f_425_, 1, v_inst_419_);
lean_closure_set(v___f_425_, 2, v_inst_420_);
lean_closure_set(v___f_425_, 3, v_constName_421_);
v___x_426_ = lean_apply_4(v_toBind_423_, lean_box(0), lean_box(0), v_getRef_424_, v___f_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object* v_m_427_, lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_constName_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_throwUnknownConstant___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_constName_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_a_438_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v_x_437_, 1);
v___x_439_ = lean_apply_1(v_inst_436_, v_a_438_);
v___x_440_ = l_Lean_throwError___redArg(v_inst_434_, v_inst_435_, v___x_439_);
return v___x_440_;
}
else
{
lean_object* v_toApplicative_441_; lean_object* v_toPure_442_; lean_object* v_a_443_; lean_object* v___x_444_; 
v_toApplicative_441_ = lean_ctor_get(v_inst_434_, 0);
lean_inc_ref(v_toApplicative_441_);
lean_dec_ref(v_inst_436_);
lean_dec_ref(v_inst_435_);
lean_dec_ref(v_inst_434_);
v_toPure_442_ = lean_ctor_get(v_toApplicative_441_, 1);
lean_inc(v_toPure_442_);
lean_dec_ref(v_toApplicative_441_);
v_a_443_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v_x_437_, 1);
v___x_444_ = lean_apply_2(v_toPure_442_, lean_box(0), v_a_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object* v_m_445_, lean_object* v_00_u03b5_446_, lean_object* v_00_u03b1_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_ofExcept___redArg(v_inst_448_, v_inst_449_, v_inst_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_));
v___x_458_ = l_Lean_registerInternalExceptionId(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
return v_res_460_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__0(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = l_Lean_interruptExceptionId;
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object* v_inst_464_){
_start:
{
lean_object* v_toMonadExceptOf_465_; lean_object* v_throw_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_toMonadExceptOf_465_ = lean_ctor_get(v_inst_464_, 0);
lean_inc_ref(v_toMonadExceptOf_465_);
lean_dec_ref(v_inst_464_);
v_throw_466_ = lean_ctor_get(v_toMonadExceptOf_465_, 0);
lean_inc(v_throw_466_);
lean_dec_ref(v_toMonadExceptOf_465_);
v___x_467_ = lean_obj_once(&l_Lean_throwInterruptException___redArg___closed__0, &l_Lean_throwInterruptException___redArg___closed__0_once, _init_l_Lean_throwInterruptException___redArg___closed__0);
v___x_468_ = lean_apply_2(v_throw_466_, lean_box(0), v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object* v_m_469_, lean_object* v_00_u03b1_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_throwInterruptException___redArg(v_inst_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object* v_m_475_, lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_throwInterruptException(v_m_475_, v_00_u03b1_476_, v_inst_477_, v_inst_478_, v_inst_479_);
lean_dec(v_inst_479_);
lean_dec_ref(v_inst_477_);
return v_res_480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 1)
{
lean_object* v_id_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_id_482_ = lean_ctor_get(v_x_481_, 0);
v___x_483_ = l_Lean_interruptExceptionId;
v___x_484_ = l_Lean_instBEqInternalExceptionId_beq(v_id_482_, v___x_483_);
return v___x_484_;
}
else
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object* v_x_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_Lean_Exception_isInterrupt(v_x_486_);
lean_dec_ref(v_x_486_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object* v_ex_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_____do__lift_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = l_Lean_Kernel_Exception_toMessageData(v_ex_489_, v_____do__lift_492_);
v___x_494_ = l_Lean_throwError___redArg(v_inst_490_, v_inst_491_, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object* v_toBind_495_, lean_object* v_inst_496_, lean_object* v___f_497_, lean_object* v_____r_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v_inst_496_, v___f_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_ex_503_){
_start:
{
lean_object* v_toBind_504_; lean_object* v___f_505_; 
v_toBind_504_ = lean_ctor_get(v_inst_500_, 1);
lean_inc(v_toBind_504_);
lean_inc_ref(v_inst_501_);
lean_inc(v_ex_503_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__0), 4, 3);
lean_closure_set(v___f_505_, 0, v_ex_503_);
lean_closure_set(v___f_505_, 1, v_inst_500_);
lean_closure_set(v___f_505_, 2, v_inst_501_);
if (lean_obj_tag(v_ex_503_) == 16)
{
lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_inc(v_toBind_504_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1), 4, 3);
lean_closure_set(v___f_506_, 0, v_toBind_504_);
lean_closure_set(v___f_506_, 1, v_inst_502_);
lean_closure_set(v___f_506_, 2, v___f_505_);
v___x_507_ = l_Lean_throwInterruptException___redArg(v_inst_501_);
v___x_508_ = lean_apply_4(v_toBind_504_, lean_box(0), lean_box(0), v___x_507_, v___f_506_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; 
lean_dec(v_ex_503_);
lean_dec_ref(v_inst_501_);
v___x_509_ = lean_apply_4(v_toBind_504_, lean_box(0), lean_box(0), v_inst_502_, v___f_505_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object* v_m_510_, lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_ex_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_throwKernelException___redArg(v_inst_512_, v_inst_513_, v_inst_514_, v_ex_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v_x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v_x_520_, 1);
v___x_522_ = l_Lean_throwKernelException___redArg(v_inst_517_, v_inst_518_, v_inst_519_, v_a_521_);
return v___x_522_;
}
else
{
lean_object* v_toApplicative_523_; lean_object* v_toPure_524_; lean_object* v_a_525_; lean_object* v___x_526_; 
v_toApplicative_523_ = lean_ctor_get(v_inst_517_, 0);
lean_inc_ref(v_toApplicative_523_);
lean_dec(v_inst_519_);
lean_dec_ref(v_inst_518_);
lean_dec_ref(v_inst_517_);
v_toPure_524_ = lean_ctor_get(v_toApplicative_523_, 1);
lean_inc(v_toPure_524_);
lean_dec_ref(v_toApplicative_523_);
v_a_525_ = lean_ctor_get(v_x_520_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v_x_520_, 1);
v___x_526_ = lean_apply_2(v_toPure_524_, lean_box(0), v_a_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object* v_m_527_, lean_object* v_00_u03b1_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_ofExceptKernelException___redArg(v_inst_529_, v_inst_530_, v_inst_531_, v_x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object* v_inst_534_, lean_object* v_00_u03b1_535_, lean_object* v_d_536_, lean_object* v_x_537_, lean_object* v_ctx_538_){
_start:
{
lean_object* v_withRecDepth_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_withRecDepth_539_ = lean_ctor_get(v_inst_534_, 0);
lean_inc(v_withRecDepth_539_);
lean_dec_ref(v_inst_534_);
v___x_540_ = lean_apply_1(v_x_537_, v_ctx_538_);
v___x_541_ = lean_apply_3(v_withRecDepth_539_, lean_box(0), v_d_536_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object* v_inst_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_getRecDepth_544_; 
v_getRecDepth_544_ = lean_ctor_get(v_inst_542_, 1);
lean_inc(v_getRecDepth_544_);
return v_getRecDepth_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object* v_inst_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_545_, v_x_546_);
lean_dec(v_x_546_);
lean_dec_ref(v_inst_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object* v_inst_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_getMaxRecDepth_550_; 
v_getMaxRecDepth_550_ = lean_ctor_get(v_inst_548_, 2);
lean_inc(v_getMaxRecDepth_550_);
return v_getMaxRecDepth_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object* v_inst_551_, lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_551_, v_x_552_);
lean_dec(v_x_552_);
lean_dec_ref(v_inst_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object* v_inst_554_){
_start:
{
lean_object* v___f_555_; lean_object* v___f_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
lean_inc_ref_n(v_inst_554_, 2);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_555_, 0, v_inst_554_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_556_, 0, v_inst_554_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_557_, 0, v_inst_554_);
v___x_558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_558_, 0, v___f_555_);
lean_ctor_set(v___x_558_, 1, v___f_556_);
lean_ctor_set(v___x_558_, 2, v___f_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object* v_m_559_, lean_object* v_00_u03c1_560_, lean_object* v_inst_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(lean_object* v_inst_563_, lean_object* v_d_564_, lean_object* v_x_565_, lean_object* v_ctx_566_){
_start:
{
lean_object* v_withRecDepth_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_withRecDepth_567_ = lean_ctor_get(v_inst_563_, 0);
lean_inc(v_withRecDepth_567_);
lean_dec_ref(v_inst_563_);
lean_inc(v_ctx_566_);
v___x_568_ = lean_apply_1(v_x_565_, v_ctx_566_);
v___x_569_ = lean_apply_3(v_withRecDepth_567_, lean_box(0), v_d_564_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(lean_object* v_inst_570_, lean_object* v_d_571_, lean_object* v_x_572_, lean_object* v_ctx_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(v_inst_570_, v_d_571_, v_x_572_, v_ctx_573_);
lean_dec(v_ctx_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(lean_object* v_m_575_, lean_object* v_00_u03c9_576_, lean_object* v_00_u03c3_577_, lean_object* v_inst_578_, lean_object* v_00_u03b1_579_, lean_object* v_d_580_, lean_object* v_x_581_, lean_object* v_ctx_582_){
_start:
{
lean_object* v_withRecDepth_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_withRecDepth_583_ = lean_ctor_get(v_inst_578_, 0);
lean_inc(v_withRecDepth_583_);
lean_dec_ref(v_inst_578_);
lean_inc(v_ctx_582_);
v___x_584_ = lean_apply_1(v_x_581_, v_ctx_582_);
v___x_585_ = lean_apply_3(v_withRecDepth_583_, lean_box(0), v_d_580_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(lean_object* v_m_586_, lean_object* v_00_u03c9_587_, lean_object* v_00_u03c3_588_, lean_object* v_inst_589_, lean_object* v_00_u03b1_590_, lean_object* v_d_591_, lean_object* v_x_592_, lean_object* v_ctx_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(v_m_586_, v_00_u03c9_587_, v_00_u03c3_588_, v_inst_589_, v_00_u03b1_590_, v_d_591_, v_x_592_, v_ctx_593_);
lean_dec(v_ctx_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(lean_object* v_inst_595_){
_start:
{
lean_object* v_getRecDepth_596_; 
v_getRecDepth_596_ = lean_ctor_get(v_inst_595_, 1);
lean_inc(v_getRecDepth_596_);
return v_getRecDepth_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(lean_object* v_inst_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_597_);
lean_dec_ref(v_inst_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(lean_object* v_m_599_, lean_object* v_00_u03c9_600_, lean_object* v_00_u03c3_601_, lean_object* v_inst_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_getRecDepth_604_; 
v_getRecDepth_604_ = lean_ctor_get(v_inst_602_, 1);
lean_inc(v_getRecDepth_604_);
return v_getRecDepth_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(lean_object* v_m_605_, lean_object* v_00_u03c9_606_, lean_object* v_00_u03c3_607_, lean_object* v_inst_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(v_m_605_, v_00_u03c9_606_, v_00_u03c3_607_, v_inst_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec_ref(v_inst_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(lean_object* v_inst_611_){
_start:
{
lean_object* v_getMaxRecDepth_612_; 
v_getMaxRecDepth_612_ = lean_ctor_get(v_inst_611_, 2);
lean_inc(v_getMaxRecDepth_612_);
return v_getMaxRecDepth_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(lean_object* v_inst_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_613_);
lean_dec_ref(v_inst_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(lean_object* v_m_615_, lean_object* v_00_u03c9_616_, lean_object* v_00_u03c3_617_, lean_object* v_inst_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_getMaxRecDepth_620_; 
v_getMaxRecDepth_620_ = lean_ctor_get(v_inst_618_, 2);
lean_inc(v_getMaxRecDepth_620_);
return v_getMaxRecDepth_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(lean_object* v_m_621_, lean_object* v_00_u03c9_622_, lean_object* v_00_u03c3_623_, lean_object* v_inst_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(v_m_621_, v_00_u03c9_622_, v_00_u03c3_623_, v_inst_624_, v_x_625_);
lean_dec(v_x_625_);
lean_dec_ref(v_inst_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_inc_ref_n(v_inst_627_, 2);
v___x_628_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed), 8, 4);
lean_closure_set(v___x_628_, 0, lean_box(0));
lean_closure_set(v___x_628_, 1, lean_box(0));
lean_closure_set(v___x_628_, 2, lean_box(0));
lean_closure_set(v___x_628_, 3, v_inst_627_);
v___x_629_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed), 5, 4);
lean_closure_set(v___x_629_, 0, lean_box(0));
lean_closure_set(v___x_629_, 1, lean_box(0));
lean_closure_set(v___x_629_, 2, lean_box(0));
lean_closure_set(v___x_629_, 3, v_inst_627_);
v___x_630_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed), 5, 4);
lean_closure_set(v___x_630_, 0, lean_box(0));
lean_closure_set(v___x_630_, 1, lean_box(0));
lean_closure_set(v___x_630_, 2, lean_box(0));
lean_closure_set(v___x_630_, 3, v_inst_627_);
v___x_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object* v_m_632_, lean_object* v_00_u03c9_633_, lean_object* v_00_u03c3_634_, lean_object* v_inst_635_, lean_object* v_inst_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object* v_m_638_, lean_object* v_00_u03c9_639_, lean_object* v_00_u03c3_640_, lean_object* v_inst_641_, lean_object* v_inst_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(v_m_638_, v_00_u03c9_639_, v_00_u03c3_640_, v_inst_641_, v_inst_642_);
lean_dec_ref(v_inst_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(lean_object* v_inst_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_withRecDepth_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_withRecDepth_648_ = lean_ctor_get(v_inst_644_, 0);
lean_inc(v_withRecDepth_648_);
lean_dec_ref(v_inst_644_);
lean_inc(v_a_647_);
v___x_649_ = lean_apply_1(v_a_646_, v_a_647_);
v___x_650_ = lean_apply_3(v_withRecDepth_648_, lean_box(0), v_a_645_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(lean_object* v_inst_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(v_inst_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(lean_object* v_00_u03b1_656_, lean_object* v_m_657_, lean_object* v_00_u03c9_658_, lean_object* v_00_u03b2_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_00_u03b1_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_withRecDepth_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_withRecDepth_668_ = lean_ctor_get(v_inst_663_, 0);
lean_inc(v_withRecDepth_668_);
lean_dec_ref(v_inst_663_);
lean_inc(v_a_667_);
v___x_669_ = lean_apply_1(v_a_666_, v_a_667_);
v___x_670_ = lean_apply_3(v_withRecDepth_668_, lean_box(0), v_a_665_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(lean_object* v_00_u03b1_671_, lean_object* v_m_672_, lean_object* v_00_u03c9_673_, lean_object* v_00_u03b2_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_00_u03b1_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(v_00_u03b1_671_, v_m_672_, v_00_u03c9_673_, v_00_u03b2_674_, v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_00_u03b1_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_inst_676_);
lean_dec_ref(v_inst_675_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(lean_object* v_inst_684_){
_start:
{
lean_object* v_getRecDepth_685_; 
v_getRecDepth_685_ = lean_ctor_get(v_inst_684_, 1);
lean_inc(v_getRecDepth_685_);
return v_getRecDepth_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(lean_object* v_inst_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_686_);
lean_dec_ref(v_inst_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(lean_object* v_00_u03b1_688_, lean_object* v_m_689_, lean_object* v_00_u03c9_690_, lean_object* v_00_u03b2_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_getRecDepth_697_; 
v_getRecDepth_697_ = lean_ctor_get(v_inst_695_, 1);
lean_inc(v_getRecDepth_697_);
return v_getRecDepth_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(lean_object* v_00_u03b1_698_, lean_object* v_m_699_, lean_object* v_00_u03c9_700_, lean_object* v_00_u03b2_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(v_00_u03b1_698_, v_m_699_, v_00_u03c9_700_, v_00_u03b2_701_, v_inst_702_, v_inst_703_, v_inst_704_, v_inst_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_inst_705_);
lean_dec_ref(v_inst_703_);
lean_dec_ref(v_inst_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(lean_object* v_inst_708_){
_start:
{
lean_object* v_getMaxRecDepth_709_; 
v_getMaxRecDepth_709_ = lean_ctor_get(v_inst_708_, 2);
lean_inc(v_getMaxRecDepth_709_);
return v_getMaxRecDepth_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(lean_object* v_inst_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_710_);
lean_dec_ref(v_inst_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(lean_object* v_00_u03b1_712_, lean_object* v_m_713_, lean_object* v_00_u03c9_714_, lean_object* v_00_u03b2_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_getMaxRecDepth_721_; 
v_getMaxRecDepth_721_ = lean_ctor_get(v_inst_719_, 2);
lean_inc(v_getMaxRecDepth_721_);
return v_getMaxRecDepth_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(lean_object* v_00_u03b1_722_, lean_object* v_m_723_, lean_object* v_00_u03c9_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(v_00_u03b1_722_, v_m_723_, v_00_u03c9_724_, v_00_u03b2_725_, v_inst_726_, v_inst_727_, v_inst_728_, v_inst_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_727_);
lean_dec_ref(v_inst_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc_ref_n(v_inst_735_, 2);
lean_inc_ref_n(v_inst_733_, 2);
lean_inc_ref_n(v_inst_732_, 2);
v___x_736_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed), 12, 8);
lean_closure_set(v___x_736_, 0, lean_box(0));
lean_closure_set(v___x_736_, 1, lean_box(0));
lean_closure_set(v___x_736_, 2, lean_box(0));
lean_closure_set(v___x_736_, 3, lean_box(0));
lean_closure_set(v___x_736_, 4, v_inst_732_);
lean_closure_set(v___x_736_, 5, v_inst_733_);
lean_closure_set(v___x_736_, 6, v_inst_734_);
lean_closure_set(v___x_736_, 7, v_inst_735_);
v___x_737_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed), 9, 8);
lean_closure_set(v___x_737_, 0, lean_box(0));
lean_closure_set(v___x_737_, 1, lean_box(0));
lean_closure_set(v___x_737_, 2, lean_box(0));
lean_closure_set(v___x_737_, 3, lean_box(0));
lean_closure_set(v___x_737_, 4, v_inst_732_);
lean_closure_set(v___x_737_, 5, v_inst_733_);
lean_closure_set(v___x_737_, 6, v_inst_734_);
lean_closure_set(v___x_737_, 7, v_inst_735_);
v___x_738_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed), 9, 8);
lean_closure_set(v___x_738_, 0, lean_box(0));
lean_closure_set(v___x_738_, 1, lean_box(0));
lean_closure_set(v___x_738_, 2, lean_box(0));
lean_closure_set(v___x_738_, 3, lean_box(0));
lean_closure_set(v___x_738_, 4, v_inst_732_);
lean_closure_set(v___x_738_, 5, v_inst_733_);
lean_closure_set(v___x_738_, 6, v_inst_734_);
lean_closure_set(v___x_738_, 7, v_inst_735_);
v___x_739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_739_, 0, v___x_736_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object* v_00_u03b1_740_, lean_object* v_m_741_, lean_object* v_00_u03c9_742_, lean_object* v_00_u03b2_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(v_inst_744_, v_inst_745_, v_inst_747_, v_inst_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object* v_00_u03b1_750_, lean_object* v_m_751_, lean_object* v_00_u03c9_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad(v_00_u03b1_750_, v_m_751_, v_00_u03c9_752_, v_00_u03b2_753_, v_inst_754_, v_inst_755_, v_inst_756_, v_inst_757_, v_inst_758_);
lean_dec_ref(v_inst_756_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = l_Lean_maxRecDepthErrorMessage;
v___x_766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3);
v___x_768_ = l_Lean_MessageData_ofFormat(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4);
v___x_770_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_771_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object* v_inst_772_, lean_object* v_ref_773_){
_start:
{
lean_object* v_toMonadExceptOf_774_; lean_object* v_throw_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_784_; 
v_toMonadExceptOf_774_ = lean_ctor_get(v_inst_772_, 0);
lean_inc_ref(v_toMonadExceptOf_774_);
lean_dec_ref(v_inst_772_);
v_throw_775_ = lean_ctor_get(v_toMonadExceptOf_774_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_toMonadExceptOf_774_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_toMonadExceptOf_774_, 1);
lean_dec(v_unused_785_);
v___x_777_ = v_toMonadExceptOf_774_;
v_isShared_778_ = v_isSharedCheck_784_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_throw_775_);
lean_dec(v_toMonadExceptOf_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_784_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_779_);
lean_ctor_set(v___x_777_, 0, v_ref_773_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_ref_773_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_apply_2(v_throw_775_, lean_box(0), v___x_781_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object* v_m_786_, lean_object* v_00_u03b1_787_, lean_object* v_inst_788_, lean_object* v_ref_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_788_, v_ref_789_);
return v___x_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object* v_ex_791_){
_start:
{
if (lean_obj_tag(v_ex_791_) == 0)
{
lean_object* v_msg_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_msg_792_ = lean_ctor_get(v_ex_791_, 1);
lean_inc_ref(v_msg_792_);
lean_dec_ref_known(v_ex_791_, 2);
v___x_793_ = l_Lean_MessageData_stripNestedTags(v_msg_792_);
v___x_794_ = l_Lean_MessageData_kind(v___x_793_);
lean_dec_ref(v___x_793_);
v___x_795_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_796_ = lean_name_eq(v___x_794_, v___x_795_);
lean_dec(v___x_794_);
return v___x_796_;
}
else
{
uint8_t v___x_797_; 
lean_dec_ref(v_ex_791_);
v___x_797_ = 0;
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object* v_ex_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_Exception_isMaxRecDepth(v_ex_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object* v_inst_801_, lean_object* v_____do__lift_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_801_, v_____do__lift_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object* v_curr_804_, lean_object* v_withRecDepth_805_, lean_object* v_x_806_, lean_object* v_inst_807_, lean_object* v_toBind_808_, lean_object* v___f_809_, lean_object* v_max_810_){
_start:
{
uint8_t v___y_812_; lean_object* v___x_819_; uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_nat_dec_eq(v_max_810_, v___x_819_);
v___x_821_ = lean_bool_not(v___x_820_);
if (v___x_821_ == 0)
{
v___y_812_ = v___x_821_;
goto v___jp_811_;
}
else
{
uint8_t v___x_822_; 
v___x_822_ = lean_nat_dec_eq(v_curr_804_, v_max_810_);
v___y_812_ = v___x_822_;
goto v___jp_811_;
}
v___jp_811_:
{
if (v___y_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v___f_809_);
lean_dec(v_toBind_808_);
lean_dec_ref(v_inst_807_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_curr_804_, v___x_813_);
v___x_815_ = lean_apply_3(v_withRecDepth_805_, lean_box(0), v___x_814_, v_x_806_);
return v___x_815_;
}
else
{
lean_object* v_toMonadRef_816_; lean_object* v_getRef_817_; lean_object* v___x_818_; 
lean_dec(v_x_806_);
lean_dec(v_withRecDepth_805_);
v_toMonadRef_816_ = lean_ctor_get(v_inst_807_, 1);
lean_inc_ref(v_toMonadRef_816_);
lean_dec_ref(v_inst_807_);
v_getRef_817_ = lean_ctor_get(v_toMonadRef_816_, 0);
lean_inc(v_getRef_817_);
lean_dec_ref(v_toMonadRef_816_);
v___x_818_ = lean_apply_4(v_toBind_808_, lean_box(0), lean_box(0), v_getRef_817_, v___f_809_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object* v_curr_823_, lean_object* v_withRecDepth_824_, lean_object* v_x_825_, lean_object* v_inst_826_, lean_object* v_toBind_827_, lean_object* v___f_828_, lean_object* v_max_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_withIncRecDepth___redArg___lam__1(v_curr_823_, v_withRecDepth_824_, v_x_825_, v_inst_826_, v_toBind_827_, v___f_828_, v_max_829_);
lean_dec(v_max_829_);
lean_dec(v_curr_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object* v_withRecDepth_831_, lean_object* v_x_832_, lean_object* v_inst_833_, lean_object* v_toBind_834_, lean_object* v___f_835_, lean_object* v_getMaxRecDepth_836_, lean_object* v_curr_837_){
_start:
{
lean_object* v___f_838_; lean_object* v___x_839_; 
lean_inc(v_toBind_834_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_838_, 0, v_curr_837_);
lean_closure_set(v___f_838_, 1, v_withRecDepth_831_);
lean_closure_set(v___f_838_, 2, v_x_832_);
lean_closure_set(v___f_838_, 3, v_inst_833_);
lean_closure_set(v___f_838_, 4, v_toBind_834_);
lean_closure_set(v___f_838_, 5, v___f_835_);
v___x_839_ = lean_apply_4(v_toBind_834_, lean_box(0), lean_box(0), v_getMaxRecDepth_836_, v___f_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_x_843_){
_start:
{
lean_object* v_toBind_844_; lean_object* v_withRecDepth_845_; lean_object* v_getRecDepth_846_; lean_object* v_getMaxRecDepth_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; 
v_toBind_844_ = lean_ctor_get(v_inst_840_, 1);
lean_inc_n(v_toBind_844_, 2);
lean_dec_ref(v_inst_840_);
v_withRecDepth_845_ = lean_ctor_get(v_inst_842_, 0);
lean_inc(v_withRecDepth_845_);
v_getRecDepth_846_ = lean_ctor_get(v_inst_842_, 1);
lean_inc(v_getRecDepth_846_);
v_getMaxRecDepth_847_ = lean_ctor_get(v_inst_842_, 2);
lean_inc(v_getMaxRecDepth_847_);
lean_dec_ref(v_inst_842_);
lean_inc_ref(v_inst_841_);
v___f_848_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_848_, 0, v_inst_841_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_849_, 0, v_withRecDepth_845_);
lean_closure_set(v___f_849_, 1, v_x_843_);
lean_closure_set(v___f_849_, 2, v_inst_841_);
lean_closure_set(v___f_849_, 3, v_toBind_844_);
lean_closure_set(v___f_849_, 4, v___f_848_);
lean_closure_set(v___f_849_, 5, v_getMaxRecDepth_847_);
v___x_850_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v_getRecDepth_846_, v___f_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object* v_m_851_, lean_object* v_00_u03b1_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_x_856_){
_start:
{
lean_object* v_toBind_857_; lean_object* v_withRecDepth_858_; lean_object* v_getRecDepth_859_; lean_object* v_getMaxRecDepth_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; 
v_toBind_857_ = lean_ctor_get(v_inst_853_, 1);
lean_inc_n(v_toBind_857_, 2);
lean_dec_ref(v_inst_853_);
v_withRecDepth_858_ = lean_ctor_get(v_inst_855_, 0);
lean_inc(v_withRecDepth_858_);
v_getRecDepth_859_ = lean_ctor_get(v_inst_855_, 1);
lean_inc(v_getRecDepth_859_);
v_getMaxRecDepth_860_ = lean_ctor_get(v_inst_855_, 2);
lean_inc(v_getMaxRecDepth_860_);
lean_dec_ref(v_inst_855_);
lean_inc_ref(v_inst_854_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_861_, 0, v_inst_854_);
v___f_862_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_862_, 0, v_withRecDepth_858_);
lean_closure_set(v___f_862_, 1, v_x_856_);
lean_closure_set(v___f_862_, 2, v_inst_854_);
lean_closure_set(v___f_862_, 3, v_toBind_857_);
lean_closure_set(v___f_862_, 4, v___f_861_);
lean_closure_set(v___f_862_, 5, v_getMaxRecDepth_860_);
v___x_863_ = lean_apply_4(v_toBind_857_, lean_box(0), lean_box(0), v_getRecDepth_859_, v___f_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6));
v___x_948_ = l_String_toRawSubstring_x27(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23));
v___x_985_ = l_String_toRawSubstring_x27(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object* v_x_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_termThrowError_____00__closed__2));
lean_inc(v_x_999_);
v___x_1003_ = l_Lean_Syntax_isOfKind(v_x_999_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_x_999_);
v___x_1004_ = lean_box(1);
v___x_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_1001_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = l_Lean_Syntax_getArg(v_x_999_, v___x_1006_);
lean_dec(v_x_999_);
v___x_1008_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1007_);
v___x_1009_ = l_Lean_Syntax_isOfKind(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v_quotContext_1010_; lean_object* v_currMacroScope_1011_; lean_object* v_ref_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_quotContext_1010_ = lean_ctor_get(v_a_1000_, 1);
v_currMacroScope_1011_ = lean_ctor_get(v_a_1000_, 2);
v_ref_1012_ = lean_ctor_get(v_a_1000_, 5);
v___x_1013_ = l_Lean_SourceInfo_fromRef(v_ref_1012_, v___x_1009_);
v___x_1014_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1015_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1016_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc(v_currMacroScope_1011_);
lean_inc(v_quotContext_1010_);
v___x_1017_ = l_Lean_addMacroScope(v_quotContext_1010_, v___x_1016_, v_currMacroScope_1011_);
v___x_1018_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1013_, 2);
v___x_1019_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1013_);
lean_ctor_set(v___x_1019_, 1, v___x_1015_);
lean_ctor_set(v___x_1019_, 2, v___x_1017_);
lean_ctor_set(v___x_1019_, 3, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1021_ = l_Lean_Syntax_node1(v___x_1013_, v___x_1020_, v___x_1007_);
v___x_1022_ = l_Lean_Syntax_node2(v___x_1013_, v___x_1014_, v___x_1019_, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_a_1001_);
return v___x_1023_;
}
else
{
lean_object* v_quotContext_1024_; lean_object* v_currMacroScope_1025_; lean_object* v_ref_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_quotContext_1024_ = lean_ctor_get(v_a_1000_, 1);
v_currMacroScope_1025_ = lean_ctor_get(v_a_1000_, 2);
v_ref_1026_ = lean_ctor_get(v_a_1000_, 5);
v___x_1027_ = 0;
v___x_1028_ = l_Lean_SourceInfo_fromRef(v_ref_1026_, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1030_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1031_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc_n(v_currMacroScope_1025_, 2);
lean_inc_n(v_quotContext_1024_, 2);
v___x_1032_ = l_Lean_addMacroScope(v_quotContext_1024_, v___x_1031_, v_currMacroScope_1025_);
v___x_1033_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1028_, 10);
v___x_1034_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1028_);
lean_ctor_set(v___x_1034_, 1, v___x_1030_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
lean_ctor_set(v___x_1034_, 3, v___x_1033_);
v___x_1035_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1036_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1037_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1038_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1028_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1041_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Lean_addMacroScope(v_quotContext_1024_, v___x_1042_, v_currMacroScope_1025_);
v___x_1044_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1028_);
lean_ctor_set(v___x_1045_, 1, v___x_1041_);
lean_ctor_set(v___x_1045_, 2, v___x_1043_);
lean_ctor_set(v___x_1045_, 3, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_1028_, v___x_1040_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node2(v___x_1028_, v___x_1037_, v___x_1039_, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1049_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1028_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Lean_Syntax_node2(v___x_1028_, v___x_1048_, v___x_1050_, v___x_1007_);
v___x_1052_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1028_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node3(v___x_1028_, v___x_1036_, v___x_1047_, v___x_1051_, v___x_1053_);
v___x_1055_ = l_Lean_Syntax_node1(v___x_1028_, v___x_1035_, v___x_1054_);
v___x_1056_ = l_Lean_Syntax_node2(v___x_1028_, v___x_1029_, v___x_1034_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_a_1001_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(lean_object* v_x_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(v_x_1058_, v_a_1059_, v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1061_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0));
v___x_1064_ = l_String_toRawSubstring_x27(v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object* v_x_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_termThrowErrorAt_________00__closed__1));
lean_inc(v_x_1075_);
v___x_1079_ = l_Lean_Syntax_isOfKind(v_x_1075_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v_x_1075_);
v___x_1080_ = lean_box(1);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_a_1077_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = l_Lean_Syntax_getArg(v_x_1075_, v___x_1082_);
v___x_1084_ = lean_unsigned_to_nat(2u);
v___x_1085_ = l_Lean_Syntax_getArg(v_x_1075_, v___x_1084_);
lean_dec(v_x_1075_);
v___x_1086_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1085_);
v___x_1087_ = l_Lean_Syntax_isOfKind(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v_quotContext_1088_; lean_object* v_currMacroScope_1089_; lean_object* v_ref_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_quotContext_1088_ = lean_ctor_get(v_a_1076_, 1);
v_currMacroScope_1089_ = lean_ctor_get(v_a_1076_, 2);
v_ref_1090_ = lean_ctor_get(v_a_1076_, 5);
v___x_1091_ = l_Lean_SourceInfo_fromRef(v_ref_1090_, v___x_1087_);
v___x_1092_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1093_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1094_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc(v_currMacroScope_1089_);
lean_inc(v_quotContext_1088_);
v___x_1095_ = l_Lean_addMacroScope(v_quotContext_1088_, v___x_1094_, v_currMacroScope_1089_);
v___x_1096_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1091_, 2);
v___x_1097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1091_);
lean_ctor_set(v___x_1097_, 1, v___x_1093_);
lean_ctor_set(v___x_1097_, 2, v___x_1095_);
lean_ctor_set(v___x_1097_, 3, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1099_ = l_Lean_Syntax_node2(v___x_1091_, v___x_1098_, v___x_1083_, v___x_1085_);
v___x_1100_ = l_Lean_Syntax_node2(v___x_1091_, v___x_1092_, v___x_1097_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_a_1077_);
return v___x_1101_;
}
else
{
lean_object* v_quotContext_1102_; lean_object* v_currMacroScope_1103_; lean_object* v_ref_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_quotContext_1102_ = lean_ctor_get(v_a_1076_, 1);
v_currMacroScope_1103_ = lean_ctor_get(v_a_1076_, 2);
v_ref_1104_ = lean_ctor_get(v_a_1076_, 5);
v___x_1105_ = 0;
v___x_1106_ = l_Lean_SourceInfo_fromRef(v_ref_1104_, v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1108_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1109_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc_n(v_currMacroScope_1103_, 2);
lean_inc_n(v_quotContext_1102_, 2);
v___x_1110_ = l_Lean_addMacroScope(v_quotContext_1102_, v___x_1109_, v_currMacroScope_1103_);
v___x_1111_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1106_, 10);
v___x_1112_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1106_);
lean_ctor_set(v___x_1112_, 1, v___x_1108_);
lean_ctor_set(v___x_1112_, 2, v___x_1110_);
lean_ctor_set(v___x_1112_, 3, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1114_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1115_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1116_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1106_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1119_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Lean_addMacroScope(v_quotContext_1102_, v___x_1120_, v_currMacroScope_1103_);
v___x_1122_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1123_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1106_);
lean_ctor_set(v___x_1123_, 1, v___x_1119_);
lean_ctor_set(v___x_1123_, 2, v___x_1121_);
lean_ctor_set(v___x_1123_, 3, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node1(v___x_1106_, v___x_1118_, v___x_1123_);
v___x_1125_ = l_Lean_Syntax_node2(v___x_1106_, v___x_1115_, v___x_1117_, v___x_1124_);
v___x_1126_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1127_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1106_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node2(v___x_1106_, v___x_1126_, v___x_1128_, v___x_1085_);
v___x_1130_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1106_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_Syntax_node3(v___x_1106_, v___x_1114_, v___x_1125_, v___x_1129_, v___x_1131_);
v___x_1133_ = l_Lean_Syntax_node2(v___x_1106_, v___x_1113_, v___x_1083_, v___x_1132_);
v___x_1134_ = l_Lean_Syntax_node2(v___x_1106_, v___x_1107_, v___x_1112_, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_a_1077_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(lean_object* v_x_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(v_x_1136_, v_a_1137_, v_a_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1139_;
}
}
lean_object* runtime_initialize_Lean_InternalExceptionId(uint8_t builtin);
lean_object* runtime_initialize_Lean_ErrorExplanation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Exception(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
