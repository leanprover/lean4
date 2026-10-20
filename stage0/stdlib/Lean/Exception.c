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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(lean_object* v_declHint_253_, lean_object* v_toPure_254_, lean_object* v_msg_255_, lean_object* v___x_256_, lean_object* v_env_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Name_isAnonymous(v_declHint_253_);
if (v___x_258_ == 0)
{
uint8_t v_isExporting_259_; 
v_isExporting_259_ = lean_ctor_get_uint8(v_env_257_, sizeof(void*)*13);
if (v_isExporting_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec_ref(v_env_257_);
lean_dec(v_declHint_253_);
v___x_260_ = lean_apply_2(v_toPure_254_, lean_box(0), v_msg_255_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
lean_inc_ref(v_env_257_);
v___x_261_ = l_Lean_Environment_setExporting(v_env_257_, v___x_258_);
lean_inc(v_declHint_253_);
lean_inc_ref(v___x_261_);
v___x_262_ = l_Lean_Environment_contains(v___x_261_, v_declHint_253_, v_isExporting_259_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec_ref(v___x_261_);
lean_dec_ref(v_env_257_);
lean_dec(v_declHint_253_);
v___x_263_ = lean_apply_2(v_toPure_254_, lean_box(0), v_msg_255_);
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
lean_inc(v_declHint_253_);
v___x_268_ = l_Lean_MessageData_ofConstName(v_declHint_253_, v___x_258_);
v_c_269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_269_, 0, v___x_267_);
lean_ctor_set(v_c_269_, 1, v___x_268_);
v___x_270_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_257_, v_declHint_253_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v_env_257_);
lean_dec(v_declHint_253_);
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
lean_ctor_set(v___x_276_, 0, v_msg_255_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_apply_2(v_toPure_254_, lean_box(0), v___x_276_);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; lean_object* v_moduleNames_280_; lean_object* v_mod_281_; uint8_t v___x_282_; 
v_val_278_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_270_, 1);
v___x_279_ = l_Lean_Environment_header(v_env_257_);
lean_dec_ref(v_env_257_);
v_moduleNames_280_ = lean_ctor_get(v___x_279_, 4);
lean_inc_ref(v_moduleNames_280_);
lean_dec_ref(v___x_279_);
v_mod_281_ = lean_array_get(v___x_256_, v_moduleNames_280_, v_val_278_);
lean_dec(v_val_278_);
lean_dec_ref(v_moduleNames_280_);
v___x_282_ = l_Lean_isPrivateName(v_declHint_253_);
lean_dec(v_declHint_253_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_c_269_);
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
lean_ctor_set(v___x_295_, 1, v_c_269_);
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
lean_dec_ref(v_env_257_);
lean_dec(v_declHint_253_);
v___x_305_ = lean_apply_2(v_toPure_254_, lean_box(0), v_msg_255_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed(lean_object* v_declHint_306_, lean_object* v_toPure_307_, lean_object* v_msg_308_, lean_object* v___x_309_, lean_object* v_env_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(v_declHint_306_, v_toPure_307_, v_msg_308_, v___x_309_, v_env_310_);
lean_dec(v___x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___redArg(lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_msg_314_, lean_object* v_declHint_315_){
_start:
{
lean_object* v_toApplicative_316_; lean_object* v_toBind_317_; lean_object* v_getEnv_318_; lean_object* v_toPure_319_; lean_object* v___x_320_; lean_object* v___f_321_; lean_object* v___x_322_; 
v_toApplicative_316_ = lean_ctor_get(v_inst_312_, 0);
lean_inc_ref(v_toApplicative_316_);
v_toBind_317_ = lean_ctor_get(v_inst_312_, 1);
lean_inc(v_toBind_317_);
lean_dec_ref(v_inst_312_);
v_getEnv_318_ = lean_ctor_get(v_inst_313_, 0);
lean_inc(v_getEnv_318_);
lean_dec_ref(v_inst_313_);
v_toPure_319_ = lean_ctor_get(v_toApplicative_316_, 1);
lean_inc(v_toPure_319_);
lean_dec_ref(v_toApplicative_316_);
v___x_320_ = lean_box(0);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_321_, 0, v_declHint_315_);
lean_closure_set(v___f_321_, 1, v_toPure_319_);
lean_closure_set(v___f_321_, 2, v_msg_314_);
lean_closure_set(v___f_321_, 3, v___x_320_);
v___x_322_ = lean_apply_4(v_toBind_317_, lean_box(0), lean_box(0), v_getEnv_318_, v___f_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore(lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_msg_327_, lean_object* v_declHint_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_324_, v_inst_325_, v_msg_327_, v_declHint_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___boxed(lean_object* v_m_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_msg_334_, lean_object* v_declHint_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_mkUnknownIdentifierMessageCore(v_m_330_, v_inst_331_, v_inst_332_, v_inst_333_, v_msg_334_, v_declHint_335_);
lean_dec_ref(v_inst_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(lean_object* v_toPure_337_, lean_object* v_msg_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Lean_unknownIdentifierMessageTag;
v___x_340_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_msg_338_);
v___x_341_ = lean_apply_2(v_toPure_337_, lean_box(0), v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___redArg(lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_msg_344_, lean_object* v_declHint_345_){
_start:
{
lean_object* v_toApplicative_346_; lean_object* v_toBind_347_; lean_object* v_toPure_348_; lean_object* v___x_349_; lean_object* v___f_350_; lean_object* v___x_351_; 
v_toApplicative_346_ = lean_ctor_get(v_inst_342_, 0);
v_toBind_347_ = lean_ctor_get(v_inst_342_, 1);
lean_inc(v_toBind_347_);
v_toPure_348_ = lean_ctor_get(v_toApplicative_346_, 1);
lean_inc(v_toPure_348_);
v___x_349_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(v_inst_342_, v_inst_343_, v_msg_344_, v_declHint_345_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_mkUnknownIdentifierMessage___redArg___lam__0), 2, 1);
lean_closure_set(v___f_350_, 0, v_toPure_348_);
v___x_351_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v___x_349_, v___f_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object* v_m_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_msg_356_, lean_object* v_declHint_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_353_, v_inst_354_, v_msg_356_, v_declHint_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___boxed(lean_object* v_m_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_msg_363_, lean_object* v_declHint_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_mkUnknownIdentifierMessage(v_m_359_, v_inst_360_, v_inst_361_, v_inst_362_, v_msg_363_, v_declHint_364_);
lean_dec_ref(v_inst_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg___lam__0(lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_ref_368_, lean_object* v_____do__lift_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_throwErrorAt___redArg(v_inst_366_, v_inst_367_, v_ref_368_, v_____do__lift_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_ref_374_, lean_object* v_msg_375_, lean_object* v_declHint_376_){
_start:
{
lean_object* v_toBind_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_toBind_377_ = lean_ctor_get(v_inst_371_, 1);
lean_inc(v_toBind_377_);
lean_inc_ref(v_inst_371_);
v___f_378_ = lean_alloc_closure((void*)(l_Lean_throwUnknownIdentifierAt___redArg___lam__0), 4, 3);
lean_closure_set(v___f_378_, 0, v_inst_371_);
lean_closure_set(v___f_378_, 1, v_inst_373_);
lean_closure_set(v___f_378_, 2, v_ref_374_);
v___x_379_ = l_Lean_mkUnknownIdentifierMessage___redArg(v_inst_371_, v_inst_372_, v_msg_375_, v_declHint_376_);
v___x_380_ = lean_apply_4(v_toBind_377_, lean_box(0), lean_box(0), v___x_379_, v___f_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object* v_m_381_, lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_ref_386_, lean_object* v_msg_387_, lean_object* v_declHint_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_383_, v_inst_384_, v_inst_385_, v_ref_386_, v_msg_387_, v_declHint_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__0));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___redArg___closed__2));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_ref_399_, lean_object* v_constName_400_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_401_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__1, &l_Lean_throwUnknownConstantAt___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__1);
v___x_402_ = 0;
lean_inc(v_constName_400_);
v___x_403_ = l_Lean_MessageData_ofConstName(v_constName_400_, v___x_402_);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_401_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___redArg___closed__3, &l_Lean_throwUnknownConstantAt___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___redArg___closed__3);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_throwUnknownIdentifierAt___redArg(v_inst_396_, v_inst_397_, v_inst_398_, v_ref_399_, v___x_406_, v_constName_400_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object* v_m_408_, lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_ref_413_, lean_object* v_constName_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_410_, v_inst_411_, v_inst_412_, v_ref_413_, v_constName_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_constName_419_, lean_object* v_____do__lift_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_416_, v_inst_417_, v_inst_418_, v_____do__lift_420_, v_constName_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_constName_425_){
_start:
{
lean_object* v_toMonadRef_426_; lean_object* v_toBind_427_; lean_object* v_getRef_428_; lean_object* v___f_429_; lean_object* v___x_430_; 
v_toMonadRef_426_ = lean_ctor_get(v_inst_424_, 1);
v_toBind_427_ = lean_ctor_get(v_inst_422_, 1);
lean_inc(v_toBind_427_);
v_getRef_428_ = lean_ctor_get(v_toMonadRef_426_, 0);
lean_inc(v_getRef_428_);
v___f_429_ = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___redArg___lam__0), 5, 4);
lean_closure_set(v___f_429_, 0, v_inst_422_);
lean_closure_set(v___f_429_, 1, v_inst_423_);
lean_closure_set(v___f_429_, 2, v_inst_424_);
lean_closure_set(v___f_429_, 3, v_constName_425_);
v___x_430_ = lean_apply_4(v_toBind_427_, lean_box(0), lean_box(0), v_getRef_428_, v___f_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object* v_m_431_, lean_object* v_00_u03b1_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_constName_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_throwUnknownConstant___redArg(v_inst_433_, v_inst_434_, v_inst_435_, v_constName_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_a_442_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v_x_441_, 1);
v___x_443_ = lean_apply_1(v_inst_440_, v_a_442_);
v___x_444_ = l_Lean_throwError___redArg(v_inst_438_, v_inst_439_, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v_toApplicative_445_; lean_object* v_toPure_446_; lean_object* v_a_447_; lean_object* v___x_448_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_438_, 0);
lean_inc_ref(v_toApplicative_445_);
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
lean_dec_ref(v_inst_438_);
v_toPure_446_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc(v_toPure_446_);
lean_dec_ref(v_toApplicative_445_);
v_a_447_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_x_441_, 1);
v___x_448_ = lean_apply_2(v_toPure_446_, lean_box(0), v_a_447_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object* v_m_449_, lean_object* v_00_u03b5_450_, lean_object* v_00_u03b1_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_ofExcept___redArg(v_inst_452_, v_inst_453_, v_inst_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_));
v___x_462_ = l_Lean_registerInternalExceptionId(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
return v_res_464_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = l_Lean_interruptExceptionId;
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object* v_inst_468_){
_start:
{
lean_object* v_toMonadExceptOf_469_; lean_object* v_throw_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_toMonadExceptOf_469_ = lean_ctor_get(v_inst_468_, 0);
lean_inc_ref(v_toMonadExceptOf_469_);
lean_dec_ref(v_inst_468_);
v_throw_470_ = lean_ctor_get(v_toMonadExceptOf_469_, 0);
lean_inc(v_throw_470_);
lean_dec_ref(v_toMonadExceptOf_469_);
v___x_471_ = lean_obj_once(&l_Lean_throwInterruptException___redArg___closed__0, &l_Lean_throwInterruptException___redArg___closed__0_once, _init_l_Lean_throwInterruptException___redArg___closed__0);
v___x_472_ = lean_apply_2(v_throw_470_, lean_box(0), v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object* v_m_473_, lean_object* v_00_u03b1_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_throwInterruptException___redArg(v_inst_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object* v_m_479_, lean_object* v_00_u03b1_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_throwInterruptException(v_m_479_, v_00_u03b1_480_, v_inst_481_, v_inst_482_, v_inst_483_);
lean_dec_ref(v_inst_483_);
lean_dec_ref(v_inst_481_);
return v_res_484_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 1)
{
lean_object* v_id_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_id_486_ = lean_ctor_get(v_x_485_, 0);
v___x_487_ = l_Lean_interruptExceptionId;
v___x_488_ = l_Lean_instBEqInternalExceptionId_beq(v_id_486_, v___x_487_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_Exception_isInterrupt(v_x_490_);
lean_dec_ref(v_x_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object* v_ex_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_____do__lift_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = l_Lean_Kernel_Exception_toMessageData(v_ex_493_, v_____do__lift_496_);
v___x_498_ = l_Lean_throwError___redArg(v_inst_494_, v_inst_495_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object* v_inst_499_, lean_object* v_toBind_500_, lean_object* v___f_501_, lean_object* v_____r_502_){
_start:
{
lean_object* v_getOptions_503_; lean_object* v___x_504_; 
v_getOptions_503_ = lean_ctor_get(v_inst_499_, 0);
lean_inc(v_getOptions_503_);
lean_dec_ref(v_inst_499_);
v___x_504_ = lean_apply_4(v_toBind_500_, lean_box(0), lean_box(0), v_getOptions_503_, v___f_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__2(lean_object* v___f_505_, lean_object* v_____r_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_apply_1(v___f_505_, v_____r_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_ex_511_){
_start:
{
lean_object* v_toBind_512_; lean_object* v___f_513_; lean_object* v___f_514_; 
v_toBind_512_ = lean_ctor_get(v_inst_508_, 1);
lean_inc_n(v_toBind_512_, 2);
lean_inc_ref(v_inst_509_);
lean_inc(v_ex_511_);
v___f_513_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__0), 4, 3);
lean_closure_set(v___f_513_, 0, v_ex_511_);
lean_closure_set(v___f_513_, 1, v_inst_508_);
lean_closure_set(v___f_513_, 2, v_inst_509_);
lean_inc_ref(v___f_513_);
lean_inc_ref(v_inst_510_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1), 4, 3);
lean_closure_set(v___f_514_, 0, v_inst_510_);
lean_closure_set(v___f_514_, 1, v_toBind_512_);
lean_closure_set(v___f_514_, 2, v___f_513_);
if (lean_obj_tag(v_ex_511_) == 16)
{
lean_object* v___f_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v___f_513_);
lean_dec_ref(v_inst_510_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__2), 2, 1);
lean_closure_set(v___f_515_, 0, v___f_514_);
v___x_516_ = l_Lean_throwInterruptException___redArg(v_inst_509_);
v___x_517_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_516_, v___f_515_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec_ref(v___f_514_);
lean_dec(v_ex_511_);
lean_dec_ref(v_inst_509_);
v___x_518_ = lean_box(0);
v___x_519_ = l_Lean_throwKernelException___redArg___lam__1(v_inst_510_, v_toBind_512_, v___f_513_, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object* v_m_520_, lean_object* v_00_u03b1_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_ex_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_throwKernelException___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_ex_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v_x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v_x_530_, 1);
v___x_532_ = l_Lean_throwKernelException___redArg(v_inst_527_, v_inst_528_, v_inst_529_, v_a_531_);
return v___x_532_;
}
else
{
lean_object* v_toApplicative_533_; lean_object* v_toPure_534_; lean_object* v_a_535_; lean_object* v___x_536_; 
v_toApplicative_533_ = lean_ctor_get(v_inst_527_, 0);
lean_inc_ref(v_toApplicative_533_);
lean_dec_ref(v_inst_529_);
lean_dec_ref(v_inst_528_);
lean_dec_ref(v_inst_527_);
v_toPure_534_ = lean_ctor_get(v_toApplicative_533_, 1);
lean_inc(v_toPure_534_);
lean_dec_ref(v_toApplicative_533_);
v_a_535_ = lean_ctor_get(v_x_530_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v_x_530_, 1);
v___x_536_ = lean_apply_2(v_toPure_534_, lean_box(0), v_a_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object* v_m_537_, lean_object* v_00_u03b1_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_ofExceptKernelException___redArg(v_inst_539_, v_inst_540_, v_inst_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object* v_inst_544_, lean_object* v_00_u03b1_545_, lean_object* v_d_546_, lean_object* v_x_547_, lean_object* v_ctx_548_){
_start:
{
lean_object* v_withRecDepth_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_withRecDepth_549_ = lean_ctor_get(v_inst_544_, 0);
lean_inc(v_withRecDepth_549_);
lean_dec_ref(v_inst_544_);
v___x_550_ = lean_apply_1(v_x_547_, v_ctx_548_);
v___x_551_ = lean_apply_3(v_withRecDepth_549_, lean_box(0), v_d_546_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object* v_inst_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_getRecDepth_554_; 
v_getRecDepth_554_ = lean_ctor_get(v_inst_552_, 1);
lean_inc(v_getRecDepth_554_);
return v_getRecDepth_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object* v_inst_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_555_, v_x_556_);
lean_dec(v_x_556_);
lean_dec_ref(v_inst_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object* v_inst_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_getMaxRecDepth_560_; 
v_getMaxRecDepth_560_ = lean_ctor_get(v_inst_558_, 2);
lean_inc(v_getMaxRecDepth_560_);
return v_getMaxRecDepth_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object* v_inst_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_561_, v_x_562_);
lean_dec(v_x_562_);
lean_dec_ref(v_inst_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object* v_inst_564_){
_start:
{
lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___f_567_; lean_object* v___x_568_; 
lean_inc_ref_n(v_inst_564_, 2);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__0), 5, 1);
lean_closure_set(v___f_565_, 0, v_inst_564_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_566_, 0, v_inst_564_);
v___f_567_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_567_, 0, v_inst_564_);
v___x_568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_568_, 0, v___f_565_);
lean_ctor_set(v___x_568_, 1, v___f_566_);
lean_ctor_set(v___x_568_, 2, v___f_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object* v_m_569_, lean_object* v_00_u03c1_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(lean_object* v_inst_573_, lean_object* v_d_574_, lean_object* v_x_575_, lean_object* v_ctx_576_){
_start:
{
lean_object* v_withRecDepth_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_withRecDepth_577_ = lean_ctor_get(v_inst_573_, 0);
lean_inc(v_withRecDepth_577_);
lean_dec_ref(v_inst_573_);
lean_inc(v_ctx_576_);
v___x_578_ = lean_apply_1(v_x_575_, v_ctx_576_);
v___x_579_ = lean_apply_3(v_withRecDepth_577_, lean_box(0), v_d_574_, v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(lean_object* v_inst_580_, lean_object* v_d_581_, lean_object* v_x_582_, lean_object* v_ctx_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(v_inst_580_, v_d_581_, v_x_582_, v_ctx_583_);
lean_dec(v_ctx_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(lean_object* v_m_585_, lean_object* v_00_u03c9_586_, lean_object* v_00_u03c3_587_, lean_object* v_inst_588_, lean_object* v_00_u03b1_589_, lean_object* v_d_590_, lean_object* v_x_591_, lean_object* v_ctx_592_){
_start:
{
lean_object* v_withRecDepth_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_withRecDepth_593_ = lean_ctor_get(v_inst_588_, 0);
lean_inc(v_withRecDepth_593_);
lean_dec_ref(v_inst_588_);
lean_inc(v_ctx_592_);
v___x_594_ = lean_apply_1(v_x_591_, v_ctx_592_);
v___x_595_ = lean_apply_3(v_withRecDepth_593_, lean_box(0), v_d_590_, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(lean_object* v_m_596_, lean_object* v_00_u03c9_597_, lean_object* v_00_u03c3_598_, lean_object* v_inst_599_, lean_object* v_00_u03b1_600_, lean_object* v_d_601_, lean_object* v_x_602_, lean_object* v_ctx_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(v_m_596_, v_00_u03c9_597_, v_00_u03c3_598_, v_inst_599_, v_00_u03b1_600_, v_d_601_, v_x_602_, v_ctx_603_);
lean_dec(v_ctx_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(lean_object* v_inst_605_){
_start:
{
lean_object* v_getRecDepth_606_; 
v_getRecDepth_606_ = lean_ctor_get(v_inst_605_, 1);
lean_inc(v_getRecDepth_606_);
return v_getRecDepth_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(lean_object* v_inst_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_607_);
lean_dec_ref(v_inst_607_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(lean_object* v_m_609_, lean_object* v_00_u03c9_610_, lean_object* v_00_u03c3_611_, lean_object* v_inst_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_getRecDepth_614_; 
v_getRecDepth_614_ = lean_ctor_get(v_inst_612_, 1);
lean_inc(v_getRecDepth_614_);
return v_getRecDepth_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(lean_object* v_m_615_, lean_object* v_00_u03c9_616_, lean_object* v_00_u03c3_617_, lean_object* v_inst_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(v_m_615_, v_00_u03c9_616_, v_00_u03c3_617_, v_inst_618_, v_x_619_);
lean_dec(v_x_619_);
lean_dec_ref(v_inst_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(lean_object* v_inst_621_){
_start:
{
lean_object* v_getMaxRecDepth_622_; 
v_getMaxRecDepth_622_ = lean_ctor_get(v_inst_621_, 2);
lean_inc(v_getMaxRecDepth_622_);
return v_getMaxRecDepth_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(lean_object* v_inst_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_623_);
lean_dec_ref(v_inst_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(lean_object* v_m_625_, lean_object* v_00_u03c9_626_, lean_object* v_00_u03c3_627_, lean_object* v_inst_628_, lean_object* v_x_629_){
_start:
{
lean_object* v_getMaxRecDepth_630_; 
v_getMaxRecDepth_630_ = lean_ctor_get(v_inst_628_, 2);
lean_inc(v_getMaxRecDepth_630_);
return v_getMaxRecDepth_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(lean_object* v_m_631_, lean_object* v_00_u03c9_632_, lean_object* v_00_u03c3_633_, lean_object* v_inst_634_, lean_object* v_x_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(v_m_631_, v_00_u03c9_632_, v_00_u03c3_633_, v_inst_634_, v_x_635_);
lean_dec(v_x_635_);
lean_dec_ref(v_inst_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object* v_inst_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_inc_ref_n(v_inst_637_, 2);
v___x_638_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed), 8, 4);
lean_closure_set(v___x_638_, 0, lean_box(0));
lean_closure_set(v___x_638_, 1, lean_box(0));
lean_closure_set(v___x_638_, 2, lean_box(0));
lean_closure_set(v___x_638_, 3, v_inst_637_);
v___x_639_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed), 5, 4);
lean_closure_set(v___x_639_, 0, lean_box(0));
lean_closure_set(v___x_639_, 1, lean_box(0));
lean_closure_set(v___x_639_, 2, lean_box(0));
lean_closure_set(v___x_639_, 3, v_inst_637_);
v___x_640_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed), 5, 4);
lean_closure_set(v___x_640_, 0, lean_box(0));
lean_closure_set(v___x_640_, 1, lean_box(0));
lean_closure_set(v___x_640_, 2, lean_box(0));
lean_closure_set(v___x_640_, 3, v_inst_637_);
v___x_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
lean_ctor_set(v___x_641_, 2, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object* v_m_642_, lean_object* v_00_u03c9_643_, lean_object* v_00_u03c3_644_, lean_object* v_inst_645_, lean_object* v_inst_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object* v_m_648_, lean_object* v_00_u03c9_649_, lean_object* v_00_u03c3_650_, lean_object* v_inst_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(v_m_648_, v_00_u03c9_649_, v_00_u03c3_650_, v_inst_651_, v_inst_652_);
lean_dec_ref(v_inst_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(lean_object* v_inst_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_withRecDepth_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_withRecDepth_658_ = lean_ctor_get(v_inst_654_, 0);
lean_inc(v_withRecDepth_658_);
lean_dec_ref(v_inst_654_);
lean_inc(v_a_657_);
v___x_659_ = lean_apply_1(v_a_656_, v_a_657_);
v___x_660_ = lean_apply_3(v_withRecDepth_658_, lean_box(0), v_a_655_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(lean_object* v_inst_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(v_inst_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(lean_object* v_00_u03b1_666_, lean_object* v_m_667_, lean_object* v_00_u03c9_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_00_u03b1_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_withRecDepth_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_withRecDepth_678_ = lean_ctor_get(v_inst_673_, 0);
lean_inc(v_withRecDepth_678_);
lean_dec_ref(v_inst_673_);
lean_inc(v_a_677_);
v___x_679_ = lean_apply_1(v_a_676_, v_a_677_);
v___x_680_ = lean_apply_3(v_withRecDepth_678_, lean_box(0), v_a_675_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(lean_object* v_00_u03b1_681_, lean_object* v_m_682_, lean_object* v_00_u03c9_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_00_u03b1_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(v_00_u03b1_681_, v_m_682_, v_00_u03c9_683_, v_00_u03b2_684_, v_inst_685_, v_inst_686_, v_inst_687_, v_inst_688_, v_00_u03b1_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_inst_686_);
lean_dec_ref(v_inst_685_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(lean_object* v_inst_694_){
_start:
{
lean_object* v_getRecDepth_695_; 
v_getRecDepth_695_ = lean_ctor_get(v_inst_694_, 1);
lean_inc(v_getRecDepth_695_);
return v_getRecDepth_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(lean_object* v_inst_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_696_);
lean_dec_ref(v_inst_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(lean_object* v_00_u03b1_698_, lean_object* v_m_699_, lean_object* v_00_u03c9_700_, lean_object* v_00_u03b2_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_getRecDepth_707_; 
v_getRecDepth_707_ = lean_ctor_get(v_inst_705_, 1);
lean_inc(v_getRecDepth_707_);
return v_getRecDepth_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(lean_object* v_00_u03b1_708_, lean_object* v_m_709_, lean_object* v_00_u03c9_710_, lean_object* v_00_u03b2_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(v_00_u03b1_708_, v_m_709_, v_00_u03c9_710_, v_00_u03b2_711_, v_inst_712_, v_inst_713_, v_inst_714_, v_inst_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_inst_713_);
lean_dec_ref(v_inst_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(lean_object* v_inst_718_){
_start:
{
lean_object* v_getMaxRecDepth_719_; 
v_getMaxRecDepth_719_ = lean_ctor_get(v_inst_718_, 2);
lean_inc(v_getMaxRecDepth_719_);
return v_getMaxRecDepth_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(lean_object* v_inst_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_720_);
lean_dec_ref(v_inst_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(lean_object* v_00_u03b1_722_, lean_object* v_m_723_, lean_object* v_00_u03c9_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_getMaxRecDepth_731_; 
v_getMaxRecDepth_731_ = lean_ctor_get(v_inst_729_, 2);
lean_inc(v_getMaxRecDepth_731_);
return v_getMaxRecDepth_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(lean_object* v_00_u03b1_732_, lean_object* v_m_733_, lean_object* v_00_u03c9_734_, lean_object* v_00_u03b2_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(v_00_u03b1_732_, v_m_733_, v_00_u03c9_734_, v_00_u03b2_735_, v_inst_736_, v_inst_737_, v_inst_738_, v_inst_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_inst_739_);
lean_dec_ref(v_inst_737_);
lean_dec_ref(v_inst_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_inc_ref_n(v_inst_745_, 2);
lean_inc_ref_n(v_inst_743_, 2);
lean_inc_ref_n(v_inst_742_, 2);
v___x_746_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed), 12, 8);
lean_closure_set(v___x_746_, 0, lean_box(0));
lean_closure_set(v___x_746_, 1, lean_box(0));
lean_closure_set(v___x_746_, 2, lean_box(0));
lean_closure_set(v___x_746_, 3, lean_box(0));
lean_closure_set(v___x_746_, 4, v_inst_742_);
lean_closure_set(v___x_746_, 5, v_inst_743_);
lean_closure_set(v___x_746_, 6, v_inst_744_);
lean_closure_set(v___x_746_, 7, v_inst_745_);
v___x_747_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed), 9, 8);
lean_closure_set(v___x_747_, 0, lean_box(0));
lean_closure_set(v___x_747_, 1, lean_box(0));
lean_closure_set(v___x_747_, 2, lean_box(0));
lean_closure_set(v___x_747_, 3, lean_box(0));
lean_closure_set(v___x_747_, 4, v_inst_742_);
lean_closure_set(v___x_747_, 5, v_inst_743_);
lean_closure_set(v___x_747_, 6, v_inst_744_);
lean_closure_set(v___x_747_, 7, v_inst_745_);
v___x_748_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed), 9, 8);
lean_closure_set(v___x_748_, 0, lean_box(0));
lean_closure_set(v___x_748_, 1, lean_box(0));
lean_closure_set(v___x_748_, 2, lean_box(0));
lean_closure_set(v___x_748_, 3, lean_box(0));
lean_closure_set(v___x_748_, 4, v_inst_742_);
lean_closure_set(v___x_748_, 5, v_inst_743_);
lean_closure_set(v___x_748_, 6, v_inst_744_);
lean_closure_set(v___x_748_, 7, v_inst_745_);
v___x_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_749_, 0, v___x_746_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object* v_00_u03b1_750_, lean_object* v_m_751_, lean_object* v_00_u03c9_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(v_inst_754_, v_inst_755_, v_inst_757_, v_inst_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object* v_00_u03b1_760_, lean_object* v_m_761_, lean_object* v_00_u03c9_762_, lean_object* v_00_u03b2_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_inst_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad(v_00_u03b1_760_, v_m_761_, v_00_u03c9_762_, v_00_u03b2_763_, v_inst_764_, v_inst_765_, v_inst_766_, v_inst_767_, v_inst_768_);
lean_dec_ref(v_inst_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0(lean_object* v_withRecDepth_770_, lean_object* v_00_u03b1_771_, lean_object* v_d_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_apply_3(v_withRecDepth_770_, lean_box(0), v_d_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1(lean_object* v_toPure_775_, lean_object* v_____do__lift_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_____do__lift_776_);
v___x_778_ = lean_apply_2(v_toPure_775_, lean_box(0), v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad___redArg(lean_object* v_inst_779_, lean_object* v_inst_780_){
_start:
{
lean_object* v_toApplicative_781_; lean_object* v_withRecDepth_782_; lean_object* v_getRecDepth_783_; lean_object* v_getMaxRecDepth_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_797_; 
v_toApplicative_781_ = lean_ctor_get(v_inst_779_, 0);
lean_inc_ref(v_toApplicative_781_);
v_withRecDepth_782_ = lean_ctor_get(v_inst_780_, 0);
v_getRecDepth_783_ = lean_ctor_get(v_inst_780_, 1);
v_getMaxRecDepth_784_ = lean_ctor_get(v_inst_780_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_inst_780_);
if (v_isSharedCheck_797_ == 0)
{
v___x_786_ = v_inst_780_;
v_isShared_787_ = v_isSharedCheck_797_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_getMaxRecDepth_784_);
lean_inc(v_getRecDepth_783_);
lean_inc(v_withRecDepth_782_);
lean_dec(v_inst_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_797_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_toBind_788_; lean_object* v_toPure_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v_toBind_788_ = lean_ctor_get(v_inst_779_, 1);
lean_inc_n(v_toBind_788_, 2);
lean_dec_ref(v_inst_779_);
v_toPure_789_ = lean_ctor_get(v_toApplicative_781_, 1);
lean_inc(v_toPure_789_);
lean_dec_ref(v_toApplicative_781_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_790_, 0, v_withRecDepth_782_);
v___f_791_ = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthOptionTOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_791_, 0, v_toPure_789_);
lean_inc_ref(v___f_791_);
v___x_792_ = lean_apply_4(v_toBind_788_, lean_box(0), lean_box(0), v_getRecDepth_783_, v___f_791_);
v___x_793_ = lean_apply_4(v_toBind_788_, lean_box(0), lean_box(0), v_getMaxRecDepth_784_, v___f_791_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 2, v___x_793_);
lean_ctor_set(v___x_786_, 1, v___x_792_);
lean_ctor_set(v___x_786_, 0, v___f_790_);
v___x_795_ = v___x_786_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___f_790_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthOptionTOfMonad(lean_object* v_m_798_, lean_object* v_inst_799_, lean_object* v_inst_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_instMonadRecDepthOptionTOfMonad___redArg(v_inst_799_, v_inst_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = l_Lean_maxRecDepthErrorMessage;
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3);
v___x_810_ = l_Lean_MessageData_ofFormat(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4);
v___x_812_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_813_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object* v_inst_814_, lean_object* v_ref_815_){
_start:
{
lean_object* v_toMonadExceptOf_816_; lean_object* v_throw_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_826_; 
v_toMonadExceptOf_816_ = lean_ctor_get(v_inst_814_, 0);
lean_inc_ref(v_toMonadExceptOf_816_);
lean_dec_ref(v_inst_814_);
v_throw_817_ = lean_ctor_get(v_toMonadExceptOf_816_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_toMonadExceptOf_816_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_toMonadExceptOf_816_, 1);
lean_dec(v_unused_827_);
v___x_819_ = v_toMonadExceptOf_816_;
v_isShared_820_ = v_isSharedCheck_826_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_throw_817_);
lean_dec(v_toMonadExceptOf_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_826_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v___x_821_);
lean_ctor_set(v___x_819_, 0, v_ref_815_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_ref_815_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_821_);
v___x_823_ = v_reuseFailAlloc_825_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; 
v___x_824_ = lean_apply_2(v_throw_817_, lean_box(0), v___x_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object* v_m_828_, lean_object* v_00_u03b1_829_, lean_object* v_inst_830_, lean_object* v_ref_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_830_, v_ref_831_);
return v___x_832_;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object* v_ex_833_){
_start:
{
if (lean_obj_tag(v_ex_833_) == 0)
{
lean_object* v_msg_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v_msg_834_ = lean_ctor_get(v_ex_833_, 1);
lean_inc_ref(v_msg_834_);
lean_dec_ref_known(v_ex_833_, 2);
v___x_835_ = l_Lean_MessageData_stripNestedTags(v_msg_834_);
v___x_836_ = l_Lean_MessageData_kind(v___x_835_);
lean_dec_ref(v___x_835_);
v___x_837_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___redArg___closed__2));
v___x_838_ = lean_name_eq(v___x_836_, v___x_837_);
lean_dec(v___x_836_);
return v___x_838_;
}
else
{
uint8_t v___x_839_; 
lean_dec_ref(v_ex_833_);
v___x_839_ = 0;
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object* v_ex_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lean_Exception_isMaxRecDepth(v_ex_840_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object* v_inst_843_, lean_object* v_____do__lift_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_843_, v_____do__lift_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object* v_curr_846_, lean_object* v_withRecDepth_847_, lean_object* v_x_848_, lean_object* v_toMonadRef_849_, lean_object* v_toBind_850_, lean_object* v___f_851_, lean_object* v_max_852_){
_start:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_nat_dec_eq(v_max_852_, v___x_857_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_eq(v_curr_846_, v_max_852_);
if (v___x_859_ == 0)
{
lean_dec(v___f_851_);
lean_dec(v_toBind_850_);
lean_dec_ref(v_toMonadRef_849_);
goto v___jp_853_;
}
else
{
lean_object* v_getRef_860_; lean_object* v___x_861_; 
lean_dec(v_x_848_);
lean_dec(v_withRecDepth_847_);
v_getRef_860_ = lean_ctor_get(v_toMonadRef_849_, 0);
lean_inc(v_getRef_860_);
lean_dec_ref(v_toMonadRef_849_);
v___x_861_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v_getRef_860_, v___f_851_);
return v___x_861_;
}
}
else
{
lean_dec(v___f_851_);
lean_dec(v_toBind_850_);
lean_dec_ref(v_toMonadRef_849_);
goto v___jp_853_;
}
v___jp_853_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_add(v_curr_846_, v___x_854_);
v___x_856_ = lean_apply_3(v_withRecDepth_847_, lean_box(0), v___x_855_, v_x_848_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object* v_curr_862_, lean_object* v_withRecDepth_863_, lean_object* v_x_864_, lean_object* v_toMonadRef_865_, lean_object* v_toBind_866_, lean_object* v___f_867_, lean_object* v_max_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_withIncRecDepth___redArg___lam__1(v_curr_862_, v_withRecDepth_863_, v_x_864_, v_toMonadRef_865_, v_toBind_866_, v___f_867_, v_max_868_);
lean_dec(v_max_868_);
lean_dec(v_curr_862_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object* v_withRecDepth_870_, lean_object* v_x_871_, lean_object* v_toMonadRef_872_, lean_object* v_toBind_873_, lean_object* v___f_874_, lean_object* v_getMaxRecDepth_875_, lean_object* v_curr_876_){
_start:
{
lean_object* v___f_877_; lean_object* v___x_878_; 
lean_inc(v_toBind_873_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_877_, 0, v_curr_876_);
lean_closure_set(v___f_877_, 1, v_withRecDepth_870_);
lean_closure_set(v___f_877_, 2, v_x_871_);
lean_closure_set(v___f_877_, 3, v_toMonadRef_872_);
lean_closure_set(v___f_877_, 4, v_toBind_873_);
lean_closure_set(v___f_877_, 5, v___f_874_);
v___x_878_ = lean_apply_4(v_toBind_873_, lean_box(0), lean_box(0), v_getMaxRecDepth_875_, v___f_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_x_882_){
_start:
{
lean_object* v_toBind_883_; lean_object* v_withRecDepth_884_; lean_object* v_getRecDepth_885_; lean_object* v_getMaxRecDepth_886_; lean_object* v_toMonadRef_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___x_890_; 
v_toBind_883_ = lean_ctor_get(v_inst_879_, 1);
lean_inc_n(v_toBind_883_, 2);
lean_dec_ref(v_inst_879_);
v_withRecDepth_884_ = lean_ctor_get(v_inst_881_, 0);
lean_inc(v_withRecDepth_884_);
v_getRecDepth_885_ = lean_ctor_get(v_inst_881_, 1);
lean_inc(v_getRecDepth_885_);
v_getMaxRecDepth_886_ = lean_ctor_get(v_inst_881_, 2);
lean_inc(v_getMaxRecDepth_886_);
lean_dec_ref(v_inst_881_);
v_toMonadRef_887_ = lean_ctor_get(v_inst_880_, 1);
lean_inc_ref(v_toMonadRef_887_);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_888_, 0, v_inst_880_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_889_, 0, v_withRecDepth_884_);
lean_closure_set(v___f_889_, 1, v_x_882_);
lean_closure_set(v___f_889_, 2, v_toMonadRef_887_);
lean_closure_set(v___f_889_, 3, v_toBind_883_);
lean_closure_set(v___f_889_, 4, v___f_888_);
lean_closure_set(v___f_889_, 5, v_getMaxRecDepth_886_);
v___x_890_ = lean_apply_4(v_toBind_883_, lean_box(0), lean_box(0), v_getRecDepth_885_, v___f_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object* v_m_891_, lean_object* v_00_u03b1_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_x_896_){
_start:
{
lean_object* v_toBind_897_; lean_object* v_withRecDepth_898_; lean_object* v_getRecDepth_899_; lean_object* v_getMaxRecDepth_900_; lean_object* v_toMonadRef_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___x_904_; 
v_toBind_897_ = lean_ctor_get(v_inst_893_, 1);
lean_inc_n(v_toBind_897_, 2);
lean_dec_ref(v_inst_893_);
v_withRecDepth_898_ = lean_ctor_get(v_inst_895_, 0);
lean_inc(v_withRecDepth_898_);
v_getRecDepth_899_ = lean_ctor_get(v_inst_895_, 1);
lean_inc(v_getRecDepth_899_);
v_getMaxRecDepth_900_ = lean_ctor_get(v_inst_895_, 2);
lean_inc(v_getMaxRecDepth_900_);
lean_dec_ref(v_inst_895_);
v_toMonadRef_901_ = lean_ctor_get(v_inst_894_, 1);
lean_inc_ref(v_toMonadRef_901_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(v___f_902_, 0, v_inst_894_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(v___f_903_, 0, v_withRecDepth_898_);
lean_closure_set(v___f_903_, 1, v_x_896_);
lean_closure_set(v___f_903_, 2, v_toMonadRef_901_);
lean_closure_set(v___f_903_, 3, v_toBind_897_);
lean_closure_set(v___f_903_, 4, v___f_902_);
lean_closure_set(v___f_903_, 5, v_getMaxRecDepth_900_);
v___x_904_ = lean_apply_4(v_toBind_897_, lean_box(0), lean_box(0), v_getRecDepth_899_, v___f_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6));
v___x_989_ = l_String_toRawSubstring_x27(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23));
v___x_1026_ = l_String_toRawSubstring_x27(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object* v_x_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_termThrowError_____00__closed__2));
lean_inc(v_x_1040_);
v___x_1044_ = l_Lean_Syntax_isOfKind(v_x_1040_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v_x_1040_);
v___x_1045_ = lean_box(1);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_a_1042_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = l_Lean_Syntax_getArg(v_x_1040_, v___x_1047_);
lean_dec(v_x_1040_);
v___x_1049_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1048_);
v___x_1050_ = l_Lean_Syntax_isOfKind(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v_quotContext_1051_; lean_object* v_currMacroScope_1052_; lean_object* v_ref_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_quotContext_1051_ = lean_ctor_get(v_a_1041_, 1);
v_currMacroScope_1052_ = lean_ctor_get(v_a_1041_, 2);
v_ref_1053_ = lean_ctor_get(v_a_1041_, 5);
v___x_1054_ = l_Lean_SourceInfo_fromRef(v_ref_1053_, v___x_1050_);
v___x_1055_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1056_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1057_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc(v_currMacroScope_1052_);
lean_inc(v_quotContext_1051_);
v___x_1058_ = l_Lean_addMacroScope(v_quotContext_1051_, v___x_1057_, v_currMacroScope_1052_);
v___x_1059_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1054_, 2);
v___x_1060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1054_);
lean_ctor_set(v___x_1060_, 1, v___x_1056_);
lean_ctor_set(v___x_1060_, 2, v___x_1058_);
lean_ctor_set(v___x_1060_, 3, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1062_ = l_Lean_Syntax_node1(v___x_1054_, v___x_1061_, v___x_1048_);
v___x_1063_ = l_Lean_Syntax_node2(v___x_1054_, v___x_1055_, v___x_1060_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_a_1042_);
return v___x_1064_;
}
else
{
lean_object* v_quotContext_1065_; lean_object* v_currMacroScope_1066_; lean_object* v_ref_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_quotContext_1065_ = lean_ctor_get(v_a_1041_, 1);
v_currMacroScope_1066_ = lean_ctor_get(v_a_1041_, 2);
v_ref_1067_ = lean_ctor_get(v_a_1041_, 5);
v___x_1068_ = 0;
v___x_1069_ = l_Lean_SourceInfo_fromRef(v_ref_1067_, v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1071_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
v___x_1072_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9));
lean_inc_n(v_currMacroScope_1066_, 2);
lean_inc_n(v_quotContext_1065_, 2);
v___x_1073_ = l_Lean_addMacroScope(v_quotContext_1065_, v___x_1072_, v_currMacroScope_1066_);
v___x_1074_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13));
lean_inc_n(v___x_1069_, 10);
v___x_1075_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1069_);
lean_ctor_set(v___x_1075_, 1, v___x_1071_);
lean_ctor_set(v___x_1075_, 2, v___x_1073_);
lean_ctor_set(v___x_1075_, 3, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1077_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1078_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1079_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1069_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1082_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1083_ = lean_box(0);
v___x_1084_ = l_Lean_addMacroScope(v_quotContext_1065_, v___x_1083_, v_currMacroScope_1066_);
v___x_1085_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1086_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1069_);
lean_ctor_set(v___x_1086_, 1, v___x_1082_);
lean_ctor_set(v___x_1086_, 2, v___x_1084_);
lean_ctor_set(v___x_1086_, 3, v___x_1085_);
v___x_1087_ = l_Lean_Syntax_node1(v___x_1069_, v___x_1081_, v___x_1086_);
v___x_1088_ = l_Lean_Syntax_node2(v___x_1069_, v___x_1078_, v___x_1080_, v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1090_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1069_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_Syntax_node2(v___x_1069_, v___x_1089_, v___x_1091_, v___x_1048_);
v___x_1093_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1069_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_Syntax_node3(v___x_1069_, v___x_1077_, v___x_1088_, v___x_1092_, v___x_1094_);
v___x_1096_ = l_Lean_Syntax_node1(v___x_1069_, v___x_1076_, v___x_1095_);
v___x_1097_ = l_Lean_Syntax_node2(v___x_1069_, v___x_1070_, v___x_1075_, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1042_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(lean_object* v_x_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(v_x_1099_, v_a_1100_, v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1102_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0));
v___x_1105_ = l_String_toRawSubstring_x27(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object* v_x_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_termThrowErrorAt_________00__closed__1));
lean_inc(v_x_1116_);
v___x_1120_ = l_Lean_Syntax_isOfKind(v_x_1116_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_x_1116_);
v___x_1121_ = lean_box(1);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_a_1118_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1123_);
v___x_1125_ = lean_unsigned_to_nat(2u);
v___x_1126_ = l_Lean_Syntax_getArg(v_x_1116_, v___x_1125_);
lean_dec(v_x_1116_);
v___x_1127_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1));
lean_inc(v___x_1126_);
v___x_1128_ = l_Lean_Syntax_isOfKind(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v_quotContext_1129_; lean_object* v_currMacroScope_1130_; lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_quotContext_1129_ = lean_ctor_get(v_a_1117_, 1);
v_currMacroScope_1130_ = lean_ctor_get(v_a_1117_, 2);
v_ref_1131_ = lean_ctor_get(v_a_1117_, 5);
v___x_1132_ = l_Lean_SourceInfo_fromRef(v_ref_1131_, v___x_1128_);
v___x_1133_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1134_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1135_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc(v_currMacroScope_1130_);
lean_inc(v_quotContext_1129_);
v___x_1136_ = l_Lean_addMacroScope(v_quotContext_1129_, v___x_1135_, v_currMacroScope_1130_);
v___x_1137_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1132_, 2);
v___x_1138_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1132_);
lean_ctor_set(v___x_1138_, 1, v___x_1134_);
lean_ctor_set(v___x_1138_, 2, v___x_1136_);
lean_ctor_set(v___x_1138_, 3, v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1140_ = l_Lean_Syntax_node2(v___x_1132_, v___x_1139_, v___x_1124_, v___x_1126_);
v___x_1141_ = l_Lean_Syntax_node2(v___x_1132_, v___x_1133_, v___x_1138_, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_a_1118_);
return v___x_1142_;
}
else
{
lean_object* v_quotContext_1143_; lean_object* v_currMacroScope_1144_; lean_object* v_ref_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_quotContext_1143_ = lean_ctor_get(v_a_1117_, 1);
v_currMacroScope_1144_ = lean_ctor_get(v_a_1117_, 2);
v_ref_1145_ = lean_ctor_get(v_a_1117_, 5);
v___x_1146_ = 0;
v___x_1147_ = l_Lean_SourceInfo_fromRef(v_ref_1145_, v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5));
v___x_1149_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
v___x_1150_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3));
lean_inc_n(v_currMacroScope_1144_, 2);
lean_inc_n(v_quotContext_1143_, 2);
v___x_1151_ = l_Lean_addMacroScope(v_quotContext_1143_, v___x_1150_, v_currMacroScope_1144_);
v___x_1152_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5));
lean_inc_n(v___x_1147_, 10);
v___x_1153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1147_);
lean_ctor_set(v___x_1153_, 1, v___x_1149_);
lean_ctor_set(v___x_1153_, 2, v___x_1151_);
lean_ctor_set(v___x_1153_, 3, v___x_1152_);
v___x_1154_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15));
v___x_1155_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17));
v___x_1156_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19));
v___x_1157_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20));
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1147_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22));
v___x_1160_ = lean_obj_once(&l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24, &l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_once, _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24);
v___x_1161_ = lean_box(0);
v___x_1162_ = l_Lean_addMacroScope(v_quotContext_1143_, v___x_1161_, v_currMacroScope_1144_);
v___x_1163_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27));
v___x_1164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1147_);
lean_ctor_set(v___x_1164_, 1, v___x_1160_);
lean_ctor_set(v___x_1164_, 2, v___x_1162_);
lean_ctor_set(v___x_1164_, 3, v___x_1163_);
v___x_1165_ = l_Lean_Syntax_node1(v___x_1147_, v___x_1159_, v___x_1164_);
v___x_1166_ = l_Lean_Syntax_node2(v___x_1147_, v___x_1156_, v___x_1158_, v___x_1165_);
v___x_1167_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29));
v___x_1168_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__30));
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1147_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_node2(v___x_1147_, v___x_1167_, v___x_1169_, v___x_1126_);
v___x_1171_ = ((lean_object*)(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__31));
v___x_1172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1147_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_Syntax_node3(v___x_1147_, v___x_1155_, v___x_1166_, v___x_1170_, v___x_1172_);
v___x_1174_ = l_Lean_Syntax_node2(v___x_1147_, v___x_1154_, v___x_1124_, v___x_1173_);
v___x_1175_ = l_Lean_Syntax_node2(v___x_1147_, v___x_1148_, v___x_1153_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_a_1118_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(lean_object* v_x_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(v_x_1177_, v_a_1178_, v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1180_;
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
