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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_kindOfErrorName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_MessageData_stripNestedTags(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value;
static lean_once_cell_t l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value;
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termThrowError_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value_aux_0),((lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value;
static const lean_string_object l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29 = (const lean_object*)&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value;
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
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_t_6_);
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
lean_dec_ref(v_x_42_);
return v_msg_43_;
}
else
{
lean_object* v_id_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_id_44_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_id_44_);
lean_dec_ref(v_x_42_);
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
lean_dec_ref(v_x_48_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object* v_declHint_253_, lean_object* v_toPure_254_, lean_object* v_msg_255_, lean_object* v_env_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Name_isAnonymous(v_declHint_253_);
if (v___x_257_ == 0)
{
uint8_t v_isExporting_258_; 
v_isExporting_258_ = lean_ctor_get_uint8(v_env_256_, sizeof(void*)*8);
if (v_isExporting_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_253_);
v___x_259_ = lean_apply_2(v_toPure_254_, lean_box(0), v_msg_255_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
lean_inc_ref(v_env_256_);
v___x_260_ = l_Lean_Environment_setExporting(v_env_256_, v___x_257_);
lean_inc(v_declHint_253_);
lean_inc_ref(v___x_260_);
v___x_261_ = l_Lean_Environment_contains(v___x_260_, v_declHint_253_, v_isExporting_258_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v___x_260_);
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_253_);
v___x_262_ = lean_apply_2(v_toPure_254_, lean_box(0), v_msg_255_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_c_268_; lean_object* v___x_269_; 
v___x_263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2);
v___x_264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5);
v___x_265_ = l_Lean_Options_empty;
v___x_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_266_, 0, v___x_260_);
lean_ctor_set(v___x_266_, 1, v___x_263_);
lean_ctor_set(v___x_266_, 2, v___x_264_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
lean_inc(v_declHint_253_);
v___x_267_ = l_Lean_MessageData_ofConstName(v_declHint_253_, v___x_257_);
v_c_268_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_268_, 0, v___x_266_);
lean_ctor_set(v_c_268_, 1, v___x_267_);
v___x_269_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_256_, v_declHint_253_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_253_);
v___x_270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_c_268_);
v___x_272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9);
v___x_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = l_Lean_MessageData_note(v___x_273_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v_msg_255_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_apply_2(v_toPure_254_, lean_box(0), v___x_275_);
return v___x_276_;
}
else
{
lean_object* v_val_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_mod_281_; uint8_t v___x_282_; 
v_val_277_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_val_277_);
lean_dec_ref(v___x_269_);
v___x_278_ = lean_box(0);
v___x_279_ = l_Lean_Environment_header(v_env_256_);
lean_dec_ref(v_env_256_);
v___x_280_ = l_Lean_EnvironmentHeader_moduleNames(v___x_279_);
v_mod_281_ = lean_array_get(v___x_278_, v___x_280_, v_val_277_);
lean_dec(v_val_277_);
lean_dec_ref(v___x_280_);
v___x_282_ = l_Lean_isPrivateName(v_declHint_253_);
lean_dec(v_declHint_253_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_c_268_);
v___x_285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_MessageData_ofName(v_mod_281_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_MessageData_note(v___x_290_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v_msg_255_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_apply_2(v_toPure_254_, lean_box(0), v___x_292_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_294_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_c_268_);
v___x_296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_MessageData_ofName(v_mod_281_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Lean_MessageData_note(v___x_301_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v_msg_255_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_apply_2(v_toPure_254_, lean_box(0), v___x_303_);
return v___x_304_;
}
}
}
}
}
else
{
lean_object* v___x_305_; 
lean_dec_ref(v_env_256_);
lean_dec(v_declHint_253_);
v___x_305_ = lean_apply_2(v_toPure_254_, lean_box(0), v_msg_255_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg(lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_msg_308_, lean_object* v_declHint_309_){
_start:
{
lean_object* v_toApplicative_310_; lean_object* v_toBind_311_; lean_object* v_getEnv_312_; lean_object* v_toPure_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v_toApplicative_310_ = lean_ctor_get(v_inst_306_, 0);
lean_inc_ref(v_toApplicative_310_);
v_toBind_311_ = lean_ctor_get(v_inst_306_, 1);
lean_inc(v_toBind_311_);
lean_dec_ref(v_inst_306_);
v_getEnv_312_ = lean_ctor_get(v_inst_307_, 0);
lean_inc(v_getEnv_312_);
lean_dec_ref(v_inst_307_);
v_toPure_313_ = lean_ctor_get(v_toApplicative_310_, 1);
lean_inc(v_toPure_313_);
lean_dec_ref(v_toApplicative_310_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_314_, 0, v_declHint_309_);
lean_closure_set(v___f_314_, 1, v_toPure_313_);
lean_closure_set(v___f_314_, 2, v_msg_308_);
v___x_315_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v_getEnv_312_, v___f_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore(lean_object* v_m_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_msg_320_, lean_object* v_declHint_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_317_, v_inst_318_, v_msg_320_, v_declHint_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___boxed(lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_msg_327_, lean_object* v_declHint_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_mkUnknownIdentifierMessageCore(v_m_323_, v_inst_324_, v_inst_325_, v_inst_326_, v_msg_327_, v_declHint_328_);
lean_dec_ref(v_inst_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(lean_object* v_toPure_330_, lean_object* v_msg_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Lean_unknownIdentifierMessageTag;
v___x_333_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_msg_331_);
v___x_334_ = lean_apply_2(v_toPure_330_, lean_box(0), v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_msg_337_, lean_object* v_declHint_338_){
_start:
{
lean_object* v_toApplicative_339_; lean_object* v_toBind_340_; lean_object* v_toPure_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___x_344_; 
v_toApplicative_339_ = lean_ctor_get(v_inst_335_, 0);
v_toBind_340_ = lean_ctor_get(v_inst_335_, 1);
lean_inc(v_toBind_340_);
v_toPure_341_ = lean_ctor_get(v_toApplicative_339_, 1);
lean_inc(v_toPure_341_);
v___x_342_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_335_, v_inst_336_, v_msg_337_, v_declHint_338_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_343_, 0, v_toPure_341_);
v___x_344_ = lean_apply_4(v_toBind_340_, lean_box(0), lean_box(0), v___x_342_, v___f_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object* v_m_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_msg_349_, lean_object* v_declHint_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_346_, v_inst_347_, v_msg_349_, v_declHint_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___boxed(lean_object* v_m_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_msg_356_, lean_object* v_declHint_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_mkUnknownIdentifierMessage(v_m_352_, v_inst_353_, v_inst_354_, v_inst_355_, v_msg_356_, v_declHint_357_);
lean_dec_ref(v_inst_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg___lam__0(lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_ref_361_, lean_object* v_____do__lift_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_throwErrorAt___redArg(v_inst_359_, v_inst_360_, v_ref_361_, v_____do__lift_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_ref_367_, lean_object* v_msg_368_, lean_object* v_declHint_369_){
_start:
{
lean_object* v_toBind_370_; lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_toBind_370_ = lean_ctor_get(v_inst_364_, 1);
lean_inc(v_toBind_370_);
lean_inc_ref(v_inst_364_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_throwUnknownIdentifierAt___redArg___lam__0), 4, 3);
lean_closure_set(v___f_371_, 0, v_inst_364_);
lean_closure_set(v___f_371_, 1, v_inst_366_);
lean_closure_set(v___f_371_, 2, v_ref_367_);
v___x_372_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_364_, v_inst_365_, v_msg_368_, v_declHint_369_);
v___x_373_ = lean_apply_4(v_toBind_370_, lean_box(0), lean_box(0), v___x_372_, v___f_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object* v_m_374_, lean_object* v_00_u03b1_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_ref_379_, lean_object* v_msg_380_, lean_object* v_declHint_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_376_, v_inst_377_, v_inst_378_, v_ref_379_, v_msg_380_, v_declHint_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__0));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__2));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_ref_392_, lean_object* v_constName_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_394_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__1, &l_Lean_throwUnknownConstantAt___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__1);
v___x_395_ = 0;
lean_inc(v_constName_393_);
v___x_396_ = l_Lean_MessageData_ofConstName(v_constName_393_, v___x_395_);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_394_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__3, &l_Lean_throwUnknownConstantAt___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__3);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_389_, v_inst_390_, v_inst_391_, v_ref_392_, v___x_399_, v_constName_393_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object* v_m_401_, lean_object* v_00_u03b1_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_ref_406_, lean_object* v_constName_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_403_, v_inst_404_, v_inst_405_, v_ref_406_, v_constName_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_constName_412_, lean_object* v_____do__lift_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_____do__lift_413_, v_constName_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_constName_418_){
_start:
{
lean_object* v_toMonadRef_419_; lean_object* v_toBind_420_; lean_object* v_getRef_421_; lean_object* v___f_422_; lean_object* v___x_423_; 
v_toMonadRef_419_ = lean_ctor_get(v_inst_417_, 1);
v_toBind_420_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_420_);
v_getRef_421_ = lean_ctor_get(v_toMonadRef_419_, 0);
lean_inc(v_getRef_421_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___redArg___lam__0), 5, 4);
lean_closure_set(v___f_422_, 0, v_inst_415_);
lean_closure_set(v___f_422_, 1, v_inst_416_);
lean_closure_set(v___f_422_, 2, v_inst_417_);
lean_closure_set(v___f_422_, 3, v_constName_418_);
v___x_423_ = lean_apply_4(v_toBind_420_, lean_box(0), lean_box(0), v_getRef_421_, v___f_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object* v_m_424_, lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_constName_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_throwUnknownConstant___redArg(v_inst_426_, v_inst_427_, v_inst_428_, v_constName_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref(v_x_434_);
v___x_436_ = lean_apply_1(v_inst_433_, v_a_435_);
v___x_437_ = l_Lean_throwError___redArg(v_inst_431_, v_inst_432_, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v_toApplicative_438_; lean_object* v_toPure_439_; lean_object* v_a_440_; lean_object* v___x_441_; 
v_toApplicative_438_ = lean_ctor_get(v_inst_431_, 0);
lean_inc_ref(v_toApplicative_438_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_inst_432_);
lean_dec_ref(v_inst_431_);
v_toPure_439_ = lean_ctor_get(v_toApplicative_438_, 1);
lean_inc(v_toPure_439_);
lean_dec_ref(v_toApplicative_438_);
v_a_440_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v_x_434_);
v___x_441_ = lean_apply_2(v_toPure_439_, lean_box(0), v_a_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object* v_m_442_, lean_object* v_00_u03b5_443_, lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_ofExcept___redArg(v_inst_445_, v_inst_446_, v_inst_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_));
v___x_455_ = l_Lean_registerInternalExceptionId(v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
return v_res_457_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_interruptExceptionId;
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object* v_inst_461_){
_start:
{
lean_object* v_toMonadExceptOf_462_; lean_object* v_throw_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_toMonadExceptOf_462_ = lean_ctor_get(v_inst_461_, 0);
lean_inc_ref(v_toMonadExceptOf_462_);
lean_dec_ref(v_inst_461_);
v_throw_463_ = lean_ctor_get(v_toMonadExceptOf_462_, 0);
lean_inc(v_throw_463_);
lean_dec_ref(v_toMonadExceptOf_462_);
v___x_464_ = lean_obj_once(&l_Lean_throwInterruptException___redArg___closed__0, &l_Lean_throwInterruptException___redArg___closed__0_once, _init_l_Lean_throwInterruptException___redArg___closed__0);
v___x_465_ = lean_apply_2(v_throw_463_, lean_box(0), v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object* v_m_466_, lean_object* v_00_u03b1_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_throwInterruptException___redArg(v_inst_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object* v_m_472_, lean_object* v_00_u03b1_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_throwInterruptException(v_m_472_, v_00_u03b1_473_, v_inst_474_, v_inst_475_, v_inst_476_);
lean_dec(v_inst_476_);
lean_dec_ref(v_inst_474_);
return v_res_477_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 1)
{
lean_object* v_id_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_id_479_ = lean_ctor_get(v_x_478_, 0);
v___x_480_ = l_Lean_interruptExceptionId;
v___x_481_ = l_Lean_instBEqInternalExceptionId_beq(v_id_479_, v___x_480_);
return v___x_481_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object* v_x_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Lean_Exception_isInterrupt(v_x_483_);
lean_dec_ref(v_x_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object* v_ex_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_____do__lift_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = l_Lean_Kernel_Exception_toMessageData(v_ex_486_, v_____do__lift_489_);
v___x_491_ = l_Lean_throwError___redArg(v_inst_487_, v_inst_488_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object* v_toBind_492_, lean_object* v_inst_493_, lean_object* v___f_494_, lean_object* v_____r_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_apply_4(v_toBind_492_, lean_box(0), lean_box(0), v_inst_493_, v___f_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_ex_500_){
_start:
{
lean_object* v_toBind_501_; lean_object* v___f_502_; 
v_toBind_501_ = lean_ctor_get(v_inst_497_, 1);
lean_inc(v_toBind_501_);
lean_inc_ref(v_inst_498_);
lean_inc(v_ex_500_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__0), 4, 3);
lean_closure_set(v___f_502_, 0, v_ex_500_);
lean_closure_set(v___f_502_, 1, v_inst_497_);
lean_closure_set(v___f_502_, 2, v_inst_498_);
if (lean_obj_tag(v_ex_500_) == 16)
{
lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_inc(v_toBind_501_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1), 4, 3);
lean_closure_set(v___f_503_, 0, v_toBind_501_);
lean_closure_set(v___f_503_, 1, v_inst_499_);
lean_closure_set(v___f_503_, 2, v___f_502_);
v___x_504_ = l_Lean_throwInterruptException___redArg(v_inst_498_);
v___x_505_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v___x_504_, v___f_503_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; 
lean_dec(v_ex_500_);
lean_dec_ref(v_inst_498_);
v___x_506_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v_inst_499_, v___f_502_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object* v_m_507_, lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_ex_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_throwKernelException___redArg(v_inst_509_, v_inst_510_, v_inst_511_, v_ex_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v_x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v_x_517_);
v___x_519_ = l_Lean_throwKernelException___redArg(v_inst_514_, v_inst_515_, v_inst_516_, v_a_518_);
return v___x_519_;
}
else
{
lean_object* v_toApplicative_520_; lean_object* v_toPure_521_; lean_object* v_a_522_; lean_object* v___x_523_; 
v_toApplicative_520_ = lean_ctor_get(v_inst_514_, 0);
lean_inc_ref(v_toApplicative_520_);
lean_dec(v_inst_516_);
lean_dec_ref(v_inst_515_);
lean_dec_ref(v_inst_514_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_520_, 1);
lean_inc(v_toPure_521_);
lean_dec_ref(v_toApplicative_520_);
v_a_522_ = lean_ctor_get(v_x_517_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v_x_517_);
v___x_523_ = lean_apply_2(v_toPure_521_, lean_box(0), v_a_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object* v_m_524_, lean_object* v_00_u03b1_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_ofExceptKernelException___redArg(v_inst_526_, v_inst_527_, v_inst_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object* v_inst_531_, lean_object* v_00_u03b1_532_, lean_object* v_d_533_, lean_object* v_x_534_, lean_object* v_ctx_535_){
_start:
{
lean_object* v_withRecDepth_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_withRecDepth_536_ = lean_ctor_get(v_inst_531_, 0);
lean_inc(v_withRecDepth_536_);
lean_dec_ref(v_inst_531_);
v___x_537_ = lean_apply_1(v_x_534_, v_ctx_535_);
v___x_538_ = lean_apply_3(v_withRecDepth_536_, lean_box(0), v_d_533_, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object* v_inst_539_, lean_object* v_x_540_){
_start:
{
lean_object* v_getRecDepth_541_; 
v_getRecDepth_541_ = lean_ctor_get(v_inst_539_, 1);
lean_inc(v_getRecDepth_541_);
return v_getRecDepth_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object* v_inst_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_542_, v_x_543_);
lean_dec(v_x_543_);
lean_dec_ref(v_inst_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object* v_inst_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_getMaxRecDepth_547_; 
v_getMaxRecDepth_547_ = lean_ctor_get(v_inst_545_, 2);
lean_inc(v_getMaxRecDepth_547_);
return v_getMaxRecDepth_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object* v_inst_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_548_, v_x_549_);
lean_dec(v_x_549_);
lean_dec_ref(v_inst_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object* v_inst_551_){
_start:
{
lean_object* v___f_552_; lean_object* v___f_553_; lean_object* v___f_554_; lean_object* v___x_555_; 
lean_inc_ref_n(v_inst_551_, 2);
v___f_552_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_552_, 0, v_inst_551_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_553_, 0, v_inst_551_);
v___f_554_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_554_, 0, v_inst_551_);
v___x_555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_555_, 0, v___f_552_);
lean_ctor_set(v___x_555_, 1, v___f_553_);
lean_ctor_set(v___x_555_, 2, v___f_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object* v_m_556_, lean_object* v_00_u03c1_557_, lean_object* v_inst_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(lean_object* v_inst_560_, lean_object* v_d_561_, lean_object* v_x_562_, lean_object* v_ctx_563_){
_start:
{
lean_object* v_withRecDepth_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_withRecDepth_564_ = lean_ctor_get(v_inst_560_, 0);
lean_inc(v_withRecDepth_564_);
lean_dec_ref(v_inst_560_);
lean_inc(v_ctx_563_);
v___x_565_ = lean_apply_1(v_x_562_, v_ctx_563_);
v___x_566_ = lean_apply_3(v_withRecDepth_564_, lean_box(0), v_d_561_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(lean_object* v_inst_567_, lean_object* v_d_568_, lean_object* v_x_569_, lean_object* v_ctx_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(v_inst_567_, v_d_568_, v_x_569_, v_ctx_570_);
lean_dec(v_ctx_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(lean_object* v_m_572_, lean_object* v_00_u03c9_573_, lean_object* v_00_u03c3_574_, lean_object* v_inst_575_, lean_object* v_00_u03b1_576_, lean_object* v_d_577_, lean_object* v_x_578_, lean_object* v_ctx_579_){
_start:
{
lean_object* v_withRecDepth_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_withRecDepth_580_ = lean_ctor_get(v_inst_575_, 0);
lean_inc(v_withRecDepth_580_);
lean_dec_ref(v_inst_575_);
lean_inc(v_ctx_579_);
v___x_581_ = lean_apply_1(v_x_578_, v_ctx_579_);
v___x_582_ = lean_apply_3(v_withRecDepth_580_, lean_box(0), v_d_577_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(lean_object* v_m_583_, lean_object* v_00_u03c9_584_, lean_object* v_00_u03c3_585_, lean_object* v_inst_586_, lean_object* v_00_u03b1_587_, lean_object* v_d_588_, lean_object* v_x_589_, lean_object* v_ctx_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(v_m_583_, v_00_u03c9_584_, v_00_u03c3_585_, v_inst_586_, v_00_u03b1_587_, v_d_588_, v_x_589_, v_ctx_590_);
lean_dec(v_ctx_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(lean_object* v_inst_592_){
_start:
{
lean_object* v_getRecDepth_593_; 
v_getRecDepth_593_ = lean_ctor_get(v_inst_592_, 1);
lean_inc(v_getRecDepth_593_);
return v_getRecDepth_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(lean_object* v_inst_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_594_);
lean_dec_ref(v_inst_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(lean_object* v_m_596_, lean_object* v_00_u03c9_597_, lean_object* v_00_u03c3_598_, lean_object* v_inst_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_getRecDepth_601_; 
v_getRecDepth_601_ = lean_ctor_get(v_inst_599_, 1);
lean_inc(v_getRecDepth_601_);
return v_getRecDepth_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(lean_object* v_m_602_, lean_object* v_00_u03c9_603_, lean_object* v_00_u03c3_604_, lean_object* v_inst_605_, lean_object* v_x_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(v_m_602_, v_00_u03c9_603_, v_00_u03c3_604_, v_inst_605_, v_x_606_);
lean_dec(v_x_606_);
lean_dec_ref(v_inst_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(lean_object* v_inst_608_){
_start:
{
lean_object* v_getMaxRecDepth_609_; 
v_getMaxRecDepth_609_ = lean_ctor_get(v_inst_608_, 2);
lean_inc(v_getMaxRecDepth_609_);
return v_getMaxRecDepth_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(lean_object* v_inst_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_610_);
lean_dec_ref(v_inst_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(lean_object* v_m_612_, lean_object* v_00_u03c9_613_, lean_object* v_00_u03c3_614_, lean_object* v_inst_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_getMaxRecDepth_617_; 
v_getMaxRecDepth_617_ = lean_ctor_get(v_inst_615_, 2);
lean_inc(v_getMaxRecDepth_617_);
return v_getMaxRecDepth_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(lean_object* v_m_618_, lean_object* v_00_u03c9_619_, lean_object* v_00_u03c3_620_, lean_object* v_inst_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(v_m_618_, v_00_u03c9_619_, v_00_u03c3_620_, v_inst_621_, v_x_622_);
lean_dec(v_x_622_);
lean_dec_ref(v_inst_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object* v_inst_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_inc_ref_n(v_inst_624_, 2);
v___x_625_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed), 8, 4);
lean_closure_set(v___x_625_, 0, lean_box(0));
lean_closure_set(v___x_625_, 1, lean_box(0));
lean_closure_set(v___x_625_, 2, lean_box(0));
lean_closure_set(v___x_625_, 3, v_inst_624_);
v___x_626_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed), 5, 4);
lean_closure_set(v___x_626_, 0, lean_box(0));
lean_closure_set(v___x_626_, 1, lean_box(0));
lean_closure_set(v___x_626_, 2, lean_box(0));
lean_closure_set(v___x_626_, 3, v_inst_624_);
v___x_627_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed), 5, 4);
lean_closure_set(v___x_627_, 0, lean_box(0));
lean_closure_set(v___x_627_, 1, lean_box(0));
lean_closure_set(v___x_627_, 2, lean_box(0));
lean_closure_set(v___x_627_, 3, v_inst_624_);
v___x_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_625_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object* v_m_629_, lean_object* v_00_u03c9_630_, lean_object* v_00_u03c3_631_, lean_object* v_inst_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object* v_m_635_, lean_object* v_00_u03c9_636_, lean_object* v_00_u03c3_637_, lean_object* v_inst_638_, lean_object* v_inst_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(v_m_635_, v_00_u03c9_636_, v_00_u03c3_637_, v_inst_638_, v_inst_639_);
lean_dec_ref(v_inst_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(lean_object* v_inst_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_withRecDepth_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_withRecDepth_645_ = lean_ctor_get(v_inst_641_, 0);
lean_inc(v_withRecDepth_645_);
lean_dec_ref(v_inst_641_);
lean_inc(v_a_644_);
v___x_646_ = lean_apply_1(v_a_643_, v_a_644_);
v___x_647_ = lean_apply_3(v_withRecDepth_645_, lean_box(0), v_a_642_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(lean_object* v_inst_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(v_inst_648_, v_a_649_, v_a_650_, v_a_651_);
lean_dec(v_a_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(lean_object* v_00_u03b1_653_, lean_object* v_m_654_, lean_object* v_00_u03c9_655_, lean_object* v_00_u03b2_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_00_u03b1_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_withRecDepth_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_withRecDepth_665_ = lean_ctor_get(v_inst_660_, 0);
lean_inc(v_withRecDepth_665_);
lean_dec_ref(v_inst_660_);
lean_inc(v_a_664_);
v___x_666_ = lean_apply_1(v_a_663_, v_a_664_);
v___x_667_ = lean_apply_3(v_withRecDepth_665_, lean_box(0), v_a_662_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(lean_object* v_00_u03b1_668_, lean_object* v_m_669_, lean_object* v_00_u03c9_670_, lean_object* v_00_u03b2_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_00_u03b1_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(v_00_u03b1_668_, v_m_669_, v_00_u03c9_670_, v_00_u03b2_671_, v_inst_672_, v_inst_673_, v_inst_674_, v_inst_675_, v_00_u03b1_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_inst_673_);
lean_dec_ref(v_inst_672_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(lean_object* v_inst_681_){
_start:
{
lean_object* v_getRecDepth_682_; 
v_getRecDepth_682_ = lean_ctor_get(v_inst_681_, 1);
lean_inc(v_getRecDepth_682_);
return v_getRecDepth_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(lean_object* v_inst_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_683_);
lean_dec_ref(v_inst_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(lean_object* v_00_u03b1_685_, lean_object* v_m_686_, lean_object* v_00_u03c9_687_, lean_object* v_00_u03b2_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_getRecDepth_694_; 
v_getRecDepth_694_ = lean_ctor_get(v_inst_692_, 1);
lean_inc(v_getRecDepth_694_);
return v_getRecDepth_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(lean_object* v_00_u03b1_695_, lean_object* v_m_696_, lean_object* v_00_u03c9_697_, lean_object* v_00_u03b2_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(v_00_u03b1_695_, v_m_696_, v_00_u03c9_697_, v_00_u03b2_698_, v_inst_699_, v_inst_700_, v_inst_701_, v_inst_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_inst_702_);
lean_dec_ref(v_inst_700_);
lean_dec_ref(v_inst_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(lean_object* v_inst_705_){
_start:
{
lean_object* v_getMaxRecDepth_706_; 
v_getMaxRecDepth_706_ = lean_ctor_get(v_inst_705_, 2);
lean_inc(v_getMaxRecDepth_706_);
return v_getMaxRecDepth_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(lean_object* v_inst_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_707_);
lean_dec_ref(v_inst_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(lean_object* v_00_u03b1_709_, lean_object* v_m_710_, lean_object* v_00_u03c9_711_, lean_object* v_00_u03b2_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_getMaxRecDepth_718_; 
v_getMaxRecDepth_718_ = lean_ctor_get(v_inst_716_, 2);
lean_inc(v_getMaxRecDepth_718_);
return v_getMaxRecDepth_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(lean_object* v_00_u03b1_719_, lean_object* v_m_720_, lean_object* v_00_u03c9_721_, lean_object* v_00_u03b2_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(v_00_u03b1_719_, v_m_720_, v_00_u03c9_721_, v_00_u03b2_722_, v_inst_723_, v_inst_724_, v_inst_725_, v_inst_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_inst_726_);
lean_dec_ref(v_inst_724_);
lean_dec_ref(v_inst_723_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_inst_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc_ref_n(v_inst_732_, 2);
lean_inc_ref_n(v_inst_730_, 2);
lean_inc_ref_n(v_inst_729_, 2);
v___x_733_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed), 12, 8);
lean_closure_set(v___x_733_, 0, lean_box(0));
lean_closure_set(v___x_733_, 1, lean_box(0));
lean_closure_set(v___x_733_, 2, lean_box(0));
lean_closure_set(v___x_733_, 3, lean_box(0));
lean_closure_set(v___x_733_, 4, v_inst_729_);
lean_closure_set(v___x_733_, 5, v_inst_730_);
lean_closure_set(v___x_733_, 6, v_inst_731_);
lean_closure_set(v___x_733_, 7, v_inst_732_);
v___x_734_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed), 9, 8);
lean_closure_set(v___x_734_, 0, lean_box(0));
lean_closure_set(v___x_734_, 1, lean_box(0));
lean_closure_set(v___x_734_, 2, lean_box(0));
lean_closure_set(v___x_734_, 3, lean_box(0));
lean_closure_set(v___x_734_, 4, v_inst_729_);
lean_closure_set(v___x_734_, 5, v_inst_730_);
lean_closure_set(v___x_734_, 6, v_inst_731_);
lean_closure_set(v___x_734_, 7, v_inst_732_);
v___x_735_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed), 9, 8);
lean_closure_set(v___x_735_, 0, lean_box(0));
lean_closure_set(v___x_735_, 1, lean_box(0));
lean_closure_set(v___x_735_, 2, lean_box(0));
lean_closure_set(v___x_735_, 3, lean_box(0));
lean_closure_set(v___x_735_, 4, v_inst_729_);
lean_closure_set(v___x_735_, 5, v_inst_730_);
lean_closure_set(v___x_735_, 6, v_inst_731_);
lean_closure_set(v___x_735_, 7, v_inst_732_);
v___x_736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_736_, 0, v___x_733_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object* v_00_u03b1_737_, lean_object* v_m_738_, lean_object* v_00_u03c9_739_, lean_object* v_00_u03b2_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(v_inst_741_, v_inst_742_, v_inst_744_, v_inst_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object* v_00_u03b1_747_, lean_object* v_m_748_, lean_object* v_00_u03c9_749_, lean_object* v_00_u03b2_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad(v_00_u03b1_747_, v_m_748_, v_00_u03c9_749_, v_00_u03b2_750_, v_inst_751_, v_inst_752_, v_inst_753_, v_inst_754_, v_inst_755_);
lean_dec_ref(v_inst_753_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Lean_maxRecDepthErrorMessage;
v___x_763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3);
v___x_765_ = l_Lean_MessageData_ofFormat(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4);
v___x_767_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_768_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object* v_inst_769_, lean_object* v_ref_770_){
_start:
{
lean_object* v_toMonadExceptOf_771_; lean_object* v_throw_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_781_; 
v_toMonadExceptOf_771_ = lean_ctor_get(v_inst_769_, 0);
lean_inc_ref(v_toMonadExceptOf_771_);
lean_dec_ref(v_inst_769_);
v_throw_772_ = lean_ctor_get(v_toMonadExceptOf_771_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_toMonadExceptOf_771_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_toMonadExceptOf_771_, 1);
lean_dec(v_unused_782_);
v___x_774_ = v_toMonadExceptOf_771_;
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_throw_772_);
lean_dec(v_toMonadExceptOf_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_776_);
lean_ctor_set(v___x_774_, 0, v_ref_770_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_ref_770_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_780_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; 
v___x_779_ = lean_apply_2(v_throw_772_, lean_box(0), v___x_778_);
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object* v_m_783_, lean_object* v_00_u03b1_784_, lean_object* v_inst_785_, lean_object* v_ref_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_785_, v_ref_786_);
return v___x_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object* v_ex_788_){
_start:
{
if (lean_obj_tag(v_ex_788_) == 0)
{
lean_object* v_msg_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_msg_789_ = lean_ctor_get(v_ex_788_, 1);
lean_inc_ref(v_msg_789_);
lean_dec_ref(v_ex_788_);
v___x_790_ = l_Lean_MessageData_stripNestedTags(v_msg_789_);
v___x_791_ = l_Lean_MessageData_kind(v___x_790_);
lean_dec_ref(v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_793_ = lean_name_eq(v___x_791_, v___x_792_);
lean_dec(v___x_791_);
return v___x_793_;
}
else
{
uint8_t v___x_794_; 
lean_dec_ref(v_ex_788_);
v___x_794_ = 0;
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object* v_ex_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Lean_Exception_isMaxRecDepth(v_ex_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object* v_inst_798_, lean_object* v_____do__lift_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_798_, v_____do__lift_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object* v_curr_801_, lean_object* v_withRecDepth_802_, lean_object* v_x_803_, lean_object* v_inst_804_, lean_object* v_toBind_805_, lean_object* v___f_806_, lean_object* v_max_807_){
_start:
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_nat_dec_eq(v_max_807_, v___x_812_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_eq(v_curr_801_, v_max_807_);
if (v___x_814_ == 0)
{
lean_dec(v___f_806_);
lean_dec(v_toBind_805_);
lean_dec_ref(v_inst_804_);
goto v___jp_808_;
}
else
{
lean_object* v_toMonadRef_815_; lean_object* v_getRef_816_; lean_object* v___x_817_; 
lean_dec(v_x_803_);
lean_dec(v_withRecDepth_802_);
v_toMonadRef_815_ = lean_ctor_get(v_inst_804_, 1);
lean_inc_ref(v_toMonadRef_815_);
lean_dec_ref(v_inst_804_);
v_getRef_816_ = lean_ctor_get(v_toMonadRef_815_, 0);
lean_inc(v_getRef_816_);
lean_dec_ref(v_toMonadRef_815_);
v___x_817_ = lean_apply_4(v_toBind_805_, lean_box(0), lean_box(0), v_getRef_816_, v___f_806_);
return v___x_817_;
}
}
else
{
lean_dec(v___f_806_);
lean_dec(v_toBind_805_);
lean_dec_ref(v_inst_804_);
goto v___jp_808_;
}
v___jp_808_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_curr_801_, v___x_809_);
v___x_811_ = lean_apply_3(v_withRecDepth_802_, lean_box(0), v___x_810_, v_x_803_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object* v_curr_818_, lean_object* v_withRecDepth_819_, lean_object* v_x_820_, lean_object* v_inst_821_, lean_object* v_toBind_822_, lean_object* v___f_823_, lean_object* v_max_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_withIncRecDepth___redArg___lam__1(v_curr_818_, v_withRecDepth_819_, v_x_820_, v_inst_821_, v_toBind_822_, v___f_823_, v_max_824_);
lean_dec(v_max_824_);
lean_dec(v_curr_818_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object* v_withRecDepth_826_, lean_object* v_x_827_, lean_object* v_inst_828_, lean_object* v_toBind_829_, lean_object* v___f_830_, lean_object* v_getMaxRecDepth_831_, lean_object* v_curr_832_){
_start:
{
lean_object* v___f_833_; lean_object* v___x_834_; 
lean_inc(v_toBind_829_);
v___f_833_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_833_, 0, v_curr_832_);
lean_closure_set(v___f_833_, 1, v_withRecDepth_826_);
lean_closure_set(v___f_833_, 2, v_x_827_);
lean_closure_set(v___f_833_, 3, v_inst_828_);
lean_closure_set(v___f_833_, 4, v_toBind_829_);
lean_closure_set(v___f_833_, 5, v___f_830_);
v___x_834_ = lean_apply_4(v_toBind_829_, lean_box(0), lean_box(0), v_getMaxRecDepth_831_, v___f_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_toBind_839_; lean_object* v_withRecDepth_840_; lean_object* v_getRecDepth_841_; lean_object* v_getMaxRecDepth_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; 
v_toBind_839_ = lean_ctor_get(v_inst_835_, 1);
lean_inc_n(v_toBind_839_, 2);
lean_dec_ref(v_inst_835_);
v_withRecDepth_840_ = lean_ctor_get(v_inst_837_, 0);
lean_inc(v_withRecDepth_840_);
v_getRecDepth_841_ = lean_ctor_get(v_inst_837_, 1);
lean_inc(v_getRecDepth_841_);
v_getMaxRecDepth_842_ = lean_ctor_get(v_inst_837_, 2);
lean_inc(v_getMaxRecDepth_842_);
lean_dec_ref(v_inst_837_);
lean_inc_ref(v_inst_836_);
v___f_843_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_843_, 0, v_inst_836_);
v___f_844_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_844_, 0, v_withRecDepth_840_);
lean_closure_set(v___f_844_, 1, v_x_838_);
lean_closure_set(v___f_844_, 2, v_inst_836_);
lean_closure_set(v___f_844_, 3, v_toBind_839_);
lean_closure_set(v___f_844_, 4, v___f_843_);
lean_closure_set(v___f_844_, 5, v_getMaxRecDepth_842_);
v___x_845_ = lean_apply_4(v_toBind_839_, lean_box(0), lean_box(0), v_getRecDepth_841_, v___f_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object* v_m_846_, lean_object* v_00_u03b1_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_toBind_852_; lean_object* v_withRecDepth_853_; lean_object* v_getRecDepth_854_; lean_object* v_getMaxRecDepth_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___x_858_; 
v_toBind_852_ = lean_ctor_get(v_inst_848_, 1);
lean_inc_n(v_toBind_852_, 2);
lean_dec_ref(v_inst_848_);
v_withRecDepth_853_ = lean_ctor_get(v_inst_850_, 0);
lean_inc(v_withRecDepth_853_);
v_getRecDepth_854_ = lean_ctor_get(v_inst_850_, 1);
lean_inc(v_getRecDepth_854_);
v_getMaxRecDepth_855_ = lean_ctor_get(v_inst_850_, 2);
lean_inc(v_getMaxRecDepth_855_);
lean_dec_ref(v_inst_850_);
lean_inc_ref(v_inst_849_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_856_, 0, v_inst_849_);
v___f_857_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_857_, 0, v_withRecDepth_853_);
lean_closure_set(v___f_857_, 1, v_x_851_);
lean_closure_set(v___f_857_, 2, v_inst_849_);
lean_closure_set(v___f_857_, 3, v_toBind_852_);
lean_closure_set(v___f_857_, 4, v___f_856_);
lean_closure_set(v___f_857_, 5, v_getMaxRecDepth_855_);
v___x_858_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v_getRecDepth_854_, v___f_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6));
v___x_943_ = l_String_toRawSubstring_x27(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21));
v___x_975_ = l_String_toRawSubstring_x27(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object* v_x_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_termThrowError_____00__closed__2));
lean_inc(v_x_989_);
v___x_993_ = l_Lean_Syntax_isOfKind(v_x_989_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_x_989_);
v___x_994_ = lean_box(1);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_a_991_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = l_Lean_Syntax_getArg(v_x_989_, v___x_996_);
lean_dec(v_x_989_);
v___x_998_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_997_);
v___x_999_ = l_Lean_Syntax_isOfKind(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v_quotContext_1000_; lean_object* v_currMacroScope_1001_; lean_object* v_ref_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_quotContext_1000_ = lean_ctor_get(v_a_990_, 1);
v_currMacroScope_1001_ = lean_ctor_get(v_a_990_, 2);
v_ref_1002_ = lean_ctor_get(v_a_990_, 5);
v___x_1003_ = l_Lean_SourceInfo_fromRef(v_ref_1002_, v___x_999_);
v___x_1004_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1005_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1006_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc(v_currMacroScope_1001_);
lean_inc(v_quotContext_1000_);
v___x_1007_ = l_Lean_addMacroScope(v_quotContext_1000_, v___x_1006_, v_currMacroScope_1001_);
v___x_1008_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11));
lean_inc_n(v___x_1003_, 2);
v___x_1009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1003_);
lean_ctor_set(v___x_1009_, 1, v___x_1005_);
lean_ctor_set(v___x_1009_, 2, v___x_1007_);
lean_ctor_set(v___x_1009_, 3, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
v___x_1011_ = l_Lean_Syntax_node1(v___x_1003_, v___x_1010_, v___x_997_);
v___x_1012_ = l_Lean_Syntax_node2(v___x_1003_, v___x_1004_, v___x_1009_, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_a_991_);
return v___x_1013_;
}
else
{
lean_object* v_quotContext_1014_; lean_object* v_currMacroScope_1015_; lean_object* v_ref_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_quotContext_1014_ = lean_ctor_get(v_a_990_, 1);
v_currMacroScope_1015_ = lean_ctor_get(v_a_990_, 2);
v_ref_1016_ = lean_ctor_get(v_a_990_, 5);
v___x_1017_ = 0;
v___x_1018_ = l_Lean_SourceInfo_fromRef(v_ref_1016_, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1020_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1021_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc_n(v_currMacroScope_1015_, 2);
lean_inc_n(v_quotContext_1014_, 2);
v___x_1022_ = l_Lean_addMacroScope(v_quotContext_1014_, v___x_1021_, v_currMacroScope_1015_);
v___x_1023_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11));
lean_inc_n(v___x_1018_, 10);
v___x_1024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1018_);
lean_ctor_set(v___x_1024_, 1, v___x_1020_);
lean_ctor_set(v___x_1024_, 2, v___x_1022_);
lean_ctor_set(v___x_1024_, 3, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
v___x_1026_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1027_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1028_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18));
v___x_1029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1018_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1031_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
v___x_1032_ = lean_box(0);
v___x_1033_ = l_Lean_addMacroScope(v_quotContext_1014_, v___x_1032_, v_currMacroScope_1015_);
v___x_1034_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25));
v___x_1035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1018_);
lean_ctor_set(v___x_1035_, 1, v___x_1031_);
lean_ctor_set(v___x_1035_, 2, v___x_1033_);
lean_ctor_set(v___x_1035_, 3, v___x_1034_);
v___x_1036_ = l_Lean_Syntax_node1(v___x_1018_, v___x_1030_, v___x_1035_);
v___x_1037_ = l_Lean_Syntax_node2(v___x_1018_, v___x_1027_, v___x_1029_, v___x_1036_);
v___x_1038_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1039_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28));
v___x_1040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1018_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Syntax_node2(v___x_1018_, v___x_1038_, v___x_1040_, v___x_997_);
v___x_1042_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1018_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node3(v___x_1018_, v___x_1026_, v___x_1037_, v___x_1041_, v___x_1043_);
v___x_1045_ = l_Lean_Syntax_node1(v___x_1018_, v___x_1025_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node2(v___x_1018_, v___x_1019_, v___x_1024_, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_a_991_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(lean_object* v_x_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(v_x_1048_, v_a_1049_, v_a_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0));
v___x_1054_ = l_String_toRawSubstring_x27(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object* v_x_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_termThrowErrorAt_________00__closed__1));
lean_inc(v_x_1065_);
v___x_1069_ = l_Lean_Syntax_isOfKind(v_x_1065_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_x_1065_);
v___x_1070_ = lean_box(1);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_a_1067_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1072_);
v___x_1074_ = lean_unsigned_to_nat(2u);
v___x_1075_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1074_);
lean_dec(v_x_1065_);
v___x_1076_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1075_);
v___x_1077_ = l_Lean_Syntax_isOfKind(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v_quotContext_1078_; lean_object* v_currMacroScope_1079_; lean_object* v_ref_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_quotContext_1078_ = lean_ctor_get(v_a_1066_, 1);
v_currMacroScope_1079_ = lean_ctor_get(v_a_1066_, 2);
v_ref_1080_ = lean_ctor_get(v_a_1066_, 5);
v___x_1081_ = l_Lean_SourceInfo_fromRef(v_ref_1080_, v___x_1077_);
v___x_1082_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1083_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1084_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc(v_currMacroScope_1079_);
lean_inc(v_quotContext_1078_);
v___x_1085_ = l_Lean_addMacroScope(v_quotContext_1078_, v___x_1084_, v_currMacroScope_1079_);
v___x_1086_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1081_, 2);
v___x_1087_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1081_);
lean_ctor_set(v___x_1087_, 1, v___x_1083_);
lean_ctor_set(v___x_1087_, 2, v___x_1085_);
lean_ctor_set(v___x_1087_, 3, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
v___x_1089_ = l_Lean_Syntax_node2(v___x_1081_, v___x_1088_, v___x_1073_, v___x_1075_);
v___x_1090_ = l_Lean_Syntax_node2(v___x_1081_, v___x_1082_, v___x_1087_, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_a_1067_);
return v___x_1091_;
}
else
{
lean_object* v_quotContext_1092_; lean_object* v_currMacroScope_1093_; lean_object* v_ref_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_quotContext_1092_ = lean_ctor_get(v_a_1066_, 1);
v_currMacroScope_1093_ = lean_ctor_get(v_a_1066_, 2);
v_ref_1094_ = lean_ctor_get(v_a_1066_, 5);
v___x_1095_ = 0;
v___x_1096_ = l_Lean_SourceInfo_fromRef(v_ref_1094_, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1098_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1099_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc_n(v_currMacroScope_1093_, 2);
lean_inc_n(v_quotContext_1092_, 2);
v___x_1100_ = l_Lean_addMacroScope(v_quotContext_1092_, v___x_1099_, v_currMacroScope_1093_);
v___x_1101_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1096_, 10);
v___x_1102_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1096_);
lean_ctor_set(v___x_1102_, 1, v___x_1098_);
lean_ctor_set(v___x_1102_, 2, v___x_1100_);
lean_ctor_set(v___x_1102_, 3, v___x_1101_);
v___x_1103_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
v___x_1104_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1105_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1106_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18));
v___x_1107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1096_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1109_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_addMacroScope(v_quotContext_1092_, v___x_1110_, v_currMacroScope_1093_);
v___x_1112_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25));
v___x_1113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1096_);
lean_ctor_set(v___x_1113_, 1, v___x_1109_);
lean_ctor_set(v___x_1113_, 2, v___x_1111_);
lean_ctor_set(v___x_1113_, 3, v___x_1112_);
v___x_1114_ = l_Lean_Syntax_node1(v___x_1096_, v___x_1108_, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node2(v___x_1096_, v___x_1105_, v___x_1107_, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1117_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28));
v___x_1118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1096_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node2(v___x_1096_, v___x_1116_, v___x_1118_, v___x_1075_);
v___x_1120_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1096_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node3(v___x_1096_, v___x_1104_, v___x_1115_, v___x_1119_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node2(v___x_1096_, v___x_1103_, v___x_1073_, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node2(v___x_1096_, v___x_1097_, v___x_1102_, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_a_1067_);
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(lean_object* v_x_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(v_x_1126_, v_a_1127_, v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1129_;
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
