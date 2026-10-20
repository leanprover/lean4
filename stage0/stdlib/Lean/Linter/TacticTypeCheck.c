// Lean compiler output
// Module: Lean.Linter.TacticTypeCheck
// Imports: import Lean.Elab.Command import Lean.Linter.Util import Lean.Meta.Check import Lean.Meta.Diagnostics
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
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isInstanceCore(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticCheckInstances"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(62, 15, 63, 147, 29, 186, 208, 53)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "enable the linter that type-checks every tactic goal at `.implicit` transparency"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "TacticTypeCheck"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(49, 102, 193, 192, 84, 254, 215, 146)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(116, 222, 67, 228, 15, 224, 52, 25)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(117, 55, 50, 200, 193, 197, 82, 26)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 246, 95, 93, 100, 71, 27, 119)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 8, 58, 244, 180, 197, 6, 42)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(18, 81, 58, 124, 13, 242, 246, 48)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___boxed(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = " tactic goal is not type-correct at `.implicit` transparency; "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = " some of the following as `@[implicit_reducible]`:"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nFull error:"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "initial"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "consider using propositional rewriting or marking"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__8_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__9_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "consider rephrasing the goal or marking"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__11_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__11_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__12_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "produced"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0 = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 120, 193, 102, 53, 18, 184, 230)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1 = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__0_value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2 = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_));
v___x_80_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4__spec__0(v___x_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4____boxed(lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(lean_object* v_e_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Lean_Expr_hasMVar(v_e_83_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_e_83_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; lean_object* v_mctx_89_; lean_object* v___x_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; lean_object* v___x_93_; lean_object* v_cache_94_; lean_object* v_zetaDeltaFVarIds_95_; lean_object* v_postponed_96_; lean_object* v_diag_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_106_; 
v___x_88_ = lean_st_ref_get(v___y_84_);
v_mctx_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_mctx_89_);
lean_dec(v___x_88_);
v___x_90_ = l_Lean_instantiateMVarsCore(v_mctx_89_, v_e_83_);
v_fst_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_fst_91_);
v_snd_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_snd_92_);
lean_dec_ref(v___x_90_);
v___x_93_ = lean_st_ref_take(v___y_84_);
v_cache_94_ = lean_ctor_get(v___x_93_, 1);
v_zetaDeltaFVarIds_95_ = lean_ctor_get(v___x_93_, 2);
v_postponed_96_ = lean_ctor_get(v___x_93_, 3);
v_diag_97_ = lean_ctor_get(v___x_93_, 4);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_93_, 0);
lean_dec(v_unused_107_);
v___x_99_ = v___x_93_;
v_isShared_100_ = v_isSharedCheck_106_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_diag_97_);
lean_inc(v_postponed_96_);
lean_inc(v_zetaDeltaFVarIds_95_);
lean_inc(v_cache_94_);
lean_dec(v___x_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_106_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v_snd_92_);
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_snd_92_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_cache_94_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_zetaDeltaFVarIds_95_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_postponed_96_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v_diag_97_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_st_ref_put(v___y_84_, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v_fst_91_);
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg___boxed(lean_object* v_e_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_108_, v___y_109_);
lean_dec(v___y_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(lean_object* v_e_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_112_, v___y_114_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___boxed(lean_object* v_e_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(v_e_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(lean_object* v_opts_126_, lean_object* v_opt_127_){
_start:
{
lean_object* v_name_128_; lean_object* v_defValue_129_; lean_object* v_map_130_; lean_object* v___x_131_; 
v_name_128_ = lean_ctor_get(v_opt_127_, 0);
v_defValue_129_ = lean_ctor_get(v_opt_127_, 1);
v_map_130_ = lean_ctor_get(v_opts_126_, 0);
v___x_131_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_130_, v_name_128_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_inc(v_defValue_129_);
return v_defValue_129_;
}
else
{
lean_object* v_val_132_; 
v_val_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_val_132_);
lean_dec_ref_known(v___x_131_, 1);
if (lean_obj_tag(v_val_132_) == 3)
{
lean_object* v_v_133_; 
v_v_133_ = lean_ctor_get(v_val_132_, 0);
lean_inc(v_v_133_);
lean_dec_ref_known(v_val_132_, 1);
return v_v_133_;
}
else
{
lean_dec(v_val_132_);
lean_inc(v_defValue_129_);
return v_defValue_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(lean_object* v_opts_134_, lean_object* v_opt_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_opts_134_, v_opt_135_);
lean_dec_ref(v_opt_135_);
lean_dec_ref(v_opts_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(lean_object* v_lctx_137_, lean_object* v_localInsts_138_, lean_object* v_x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_137_, v_localInsts_138_, v_x_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_145_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_145_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg___boxed(lean_object* v_lctx_162_, lean_object* v_localInsts_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(v_lctx_162_, v_localInsts_163_, v_x_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(lean_object* v_00_u03b1_171_, lean_object* v_lctx_172_, lean_object* v_localInsts_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(v_lctx_172_, v_localInsts_173_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___boxed(lean_object* v_00_u03b1_181_, lean_object* v_lctx_182_, lean_object* v_localInsts_183_, lean_object* v_x_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(v_00_u03b1_181_, v_lctx_182_, v_localInsts_183_, v_x_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(lean_object* v_opts_191_, lean_object* v_opt_192_){
_start:
{
lean_object* v_name_193_; lean_object* v_defValue_194_; lean_object* v_map_195_; lean_object* v___x_196_; 
v_name_193_ = lean_ctor_get(v_opt_192_, 0);
v_defValue_194_ = lean_ctor_get(v_opt_192_, 1);
v_map_195_ = lean_ctor_get(v_opts_191_, 0);
v___x_196_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_195_, v_name_193_);
if (lean_obj_tag(v___x_196_) == 0)
{
uint8_t v___x_197_; 
v___x_197_ = lean_unbox(v_defValue_194_);
return v___x_197_;
}
else
{
lean_object* v_val_198_; 
v_val_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v___x_196_, 1);
if (lean_obj_tag(v_val_198_) == 1)
{
uint8_t v_v_199_; 
v_v_199_ = lean_ctor_get_uint8(v_val_198_, 0);
lean_dec_ref_known(v_val_198_, 0);
return v_v_199_;
}
else
{
uint8_t v___x_200_; 
lean_dec(v_val_198_);
v___x_200_ = lean_unbox(v_defValue_194_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0___boxed(lean_object* v_opts_201_, lean_object* v_opt_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_201_, v_opt_202_);
lean_dec_ref(v_opt_202_);
lean_dec_ref(v_opts_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0(uint8_t v_suppressElabErrors_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 1)
{
lean_object* v_pre_208_; 
v_pre_208_ = lean_ctor_get(v_x_207_, 0);
if (lean_obj_tag(v_pre_208_) == 0)
{
lean_object* v_str_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_str_209_ = lean_ctor_get(v_x_207_, 1);
v___x_210_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___closed__0));
v___x_211_ = lean_string_dec_eq(v_str_209_, v___x_210_);
if (v___x_211_ == 0)
{
return v___x_211_;
}
else
{
return v_suppressElabErrors_206_;
}
}
else
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
}
else
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_214_, lean_object* v_x_215_){
_start:
{
uint8_t v_suppressElabErrors_boxed_216_; uint8_t v_res_217_; lean_object* v_r_218_; 
v_suppressElabErrors_boxed_216_ = lean_unbox(v_suppressElabErrors_214_);
v_res_217_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0(v_suppressElabErrors_boxed_216_, v_x_215_);
lean_dec(v_x_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_219_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_ctor_set(v___x_225_, 2, v___x_224_);
lean_ctor_set(v___x_225_, 3, v___x_224_);
lean_ctor_set(v___x_225_, 4, v___x_223_);
lean_ctor_set(v___x_225_, 5, v___x_223_);
lean_ctor_set(v___x_225_, 6, v___x_223_);
lean_ctor_set(v___x_225_, 7, v___x_223_);
lean_ctor_set(v___x_225_, 8, v___x_223_);
lean_ctor_set(v___x_225_, 9, v___x_223_);
lean_ctor_set(v___x_225_, 10, v___x_223_);
lean_ctor_set(v___x_225_, 11, v___x_222_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(32u);
v___x_227_ = lean_mk_empty_array_with_capacity(v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4(void){
_start:
{
size_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_229_ = ((size_t)5ULL);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_unsigned_to_nat(32u);
v___x_232_ = lean_mk_empty_array_with_capacity(v___x_231_);
v___x_233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3);
v___x_234_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_230_);
lean_ctor_set(v___x_234_, 3, v___x_230_);
lean_ctor_set_usize(v___x_234_, 4, v___x_229_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_box(1);
v___x_236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_237_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_235_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(lean_object* v_msgData_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; lean_object* v_env_243_; uint8_t v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_scopes_248_; lean_object* v___x_249_; lean_object* v_opts_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_242_ = lean_st_ref_get(v___y_240_);
v_env_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_env_243_);
lean_dec(v___x_242_);
v___x_244_ = 0;
v_env_245_ = l_Lean_Environment_setRecordingDeps(v_env_243_, v___x_244_);
v___x_246_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_247_ = lean_st_ref_get(v___y_240_);
v_scopes_248_ = lean_ctor_get(v___x_247_, 2);
lean_inc(v_scopes_248_);
lean_dec(v___x_247_);
v___x_249_ = l_List_head_x21___redArg(v___x_246_, v_scopes_248_);
lean_dec(v_scopes_248_);
v_opts_250_ = lean_ctor_get(v___x_249_, 1);
lean_inc_ref(v_opts_250_);
lean_dec(v___x_249_);
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2);
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5);
v___x_253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_253_, 0, v_env_245_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
lean_ctor_set(v___x_253_, 3, v_opts_250_);
v___x_254_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_msgData_239_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___boxed(lean_object* v_msgData_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v_msgData_256_, v___y_257_);
lean_dec(v___y_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(lean_object* v_ref_261_, lean_object* v_msgData_262_, uint8_t v_severity_263_, uint8_t v_isSilent_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; uint8_t v___y_334_; uint8_t v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; uint8_t v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; uint8_t v___y_367_; uint8_t v___y_368_; uint8_t v___x_383_; uint8_t v___y_385_; uint8_t v___x_395_; 
v___x_383_ = 2;
v___x_395_ = l_Lean_instBEqMessageSeverity_beq(v_severity_263_, v___x_383_);
if (v___x_395_ == 0)
{
v___y_385_ = v___x_395_;
goto v___jp_384_;
}
else
{
uint8_t v___x_396_; 
lean_inc_ref(v_msgData_262_);
v___x_396_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_262_);
if (v___x_396_ == 0)
{
v___y_385_ = v___x_396_;
goto v___jp_384_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_msgData_262_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
v___jp_268_:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Elab_Command_getScope___redArg(v___y_276_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v_currNamespace_279_; lean_object* v___x_280_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_277_, 1);
v_currNamespace_279_ = lean_ctor_get(v_a_278_, 2);
lean_inc(v_currNamespace_279_);
lean_dec(v_a_278_);
v___x_280_ = l_Lean_Elab_Command_getScope___redArg(v___y_276_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_316_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_316_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_316_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_316_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_openDecls_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_env_290_; lean_object* v_messages_291_; lean_object* v_scopes_292_; lean_object* v_usedQuotCtxts_293_; lean_object* v_nextMacroScope_294_; lean_object* v_maxRecDepth_295_; lean_object* v_ngen_296_; lean_object* v_auxDeclNGen_297_; lean_object* v_infoState_298_; lean_object* v_traceState_299_; lean_object* v_snapshotTasks_300_; lean_object* v_prevLinterStates_301_; lean_object* v_codeQualityEntryTasks_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_315_; 
v_openDecls_285_ = lean_ctor_get(v_a_281_, 3);
lean_inc(v_openDecls_285_);
lean_dec(v_a_281_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_currNamespace_279_);
lean_ctor_set(v___x_286_, 1, v_openDecls_285_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___y_274_);
lean_inc_ref(v___y_271_);
lean_inc_ref(v___y_275_);
v___x_288_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_288_, 0, v___y_275_);
lean_ctor_set(v___x_288_, 1, v___y_270_);
lean_ctor_set(v___x_288_, 2, v___y_273_);
lean_ctor_set(v___x_288_, 3, v___y_271_);
lean_ctor_set(v___x_288_, 4, v___x_287_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*5, v___y_269_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*5 + 1, v___y_272_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*5 + 2, v_isSilent_264_);
v___x_289_ = lean_st_ref_take(v___y_276_);
v_env_290_ = lean_ctor_get(v___x_289_, 0);
v_messages_291_ = lean_ctor_get(v___x_289_, 1);
v_scopes_292_ = lean_ctor_get(v___x_289_, 2);
v_usedQuotCtxts_293_ = lean_ctor_get(v___x_289_, 3);
v_nextMacroScope_294_ = lean_ctor_get(v___x_289_, 4);
v_maxRecDepth_295_ = lean_ctor_get(v___x_289_, 5);
v_ngen_296_ = lean_ctor_get(v___x_289_, 6);
v_auxDeclNGen_297_ = lean_ctor_get(v___x_289_, 7);
v_infoState_298_ = lean_ctor_get(v___x_289_, 8);
v_traceState_299_ = lean_ctor_get(v___x_289_, 9);
v_snapshotTasks_300_ = lean_ctor_get(v___x_289_, 10);
v_prevLinterStates_301_ = lean_ctor_get(v___x_289_, 11);
v_codeQualityEntryTasks_302_ = lean_ctor_get(v___x_289_, 12);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_315_ == 0)
{
v___x_304_ = v___x_289_;
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_codeQualityEntryTasks_302_);
lean_inc(v_prevLinterStates_301_);
lean_inc(v_snapshotTasks_300_);
lean_inc(v_traceState_299_);
lean_inc(v_infoState_298_);
lean_inc(v_auxDeclNGen_297_);
lean_inc(v_ngen_296_);
lean_inc(v_maxRecDepth_295_);
lean_inc(v_nextMacroScope_294_);
lean_inc(v_usedQuotCtxts_293_);
lean_inc(v_scopes_292_);
lean_inc(v_messages_291_);
lean_inc(v_env_290_);
lean_dec(v___x_289_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = lean_box(0);
v___x_307_ = l_Lean_MessageLog_add(v___x_288_, v_messages_291_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_env_290_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_scopes_292_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v_usedQuotCtxts_293_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v_nextMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_314_, 5, v_maxRecDepth_295_);
lean_ctor_set(v_reuseFailAlloc_314_, 6, v_ngen_296_);
lean_ctor_set(v_reuseFailAlloc_314_, 7, v_auxDeclNGen_297_);
lean_ctor_set(v_reuseFailAlloc_314_, 8, v_infoState_298_);
lean_ctor_set(v_reuseFailAlloc_314_, 9, v_traceState_299_);
lean_ctor_set(v_reuseFailAlloc_314_, 10, v_snapshotTasks_300_);
lean_ctor_set(v_reuseFailAlloc_314_, 11, v_prevLinterStates_301_);
lean_ctor_set(v_reuseFailAlloc_314_, 12, v_codeQualityEntryTasks_302_);
v___x_309_ = v_reuseFailAlloc_314_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_st_ref_put(v___y_276_, v___x_309_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_306_);
v___x_312_ = v___x_283_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_306_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_currNamespace_279_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_270_);
v_a_317_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_280_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_280_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_270_);
v_a_325_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_277_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_277_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
v___jp_333_:
{
lean_object* v_fileName_338_; lean_object* v_fileMap_339_; uint8_t v_suppressElabErrors_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_358_; 
v_fileName_338_ = lean_ctor_get(v___y_265_, 0);
v_fileMap_339_ = lean_ctor_get(v___y_265_, 1);
v_suppressElabErrors_340_ = lean_ctor_get_uint8(v___y_265_, sizeof(void*)*10);
v___x_341_ = lean_box(v_suppressElabErrors_340_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed), 2, 1);
lean_closure_set(v___f_342_, 0, v___x_341_);
v___x_343_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_262_);
v___x_344_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v___x_343_, v___y_266_);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_358_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc_ref_n(v_fileMap_339_, 2);
v___x_349_ = l_Lean_FileMap_toPosition(v_fileMap_339_, v___y_336_);
lean_dec(v___y_336_);
v___x_350_ = l_Lean_FileMap_toPosition(v_fileMap_339_, v___y_337_);
lean_dec(v___y_337_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___closed__0));
if (v_suppressElabErrors_340_ == 0)
{
lean_del_object(v___x_347_);
lean_dec_ref(v___f_342_);
v___y_269_ = v___y_334_;
v___y_270_ = v___x_349_;
v___y_271_ = v___x_352_;
v___y_272_ = v___y_335_;
v___y_273_ = v___x_351_;
v___y_274_ = v_a_345_;
v___y_275_ = v_fileName_338_;
v___y_276_ = v___y_266_;
goto v___jp_268_;
}
else
{
uint8_t v___x_353_; 
lean_inc(v_a_345_);
v___x_353_ = l_Lean_MessageData_hasTag(v___f_342_, v_a_345_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_356_; 
lean_dec_ref_known(v___x_351_, 1);
lean_dec_ref(v___x_349_);
lean_dec(v_a_345_);
v___x_354_ = lean_box(0);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_354_);
v___x_356_ = v___x_347_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_del_object(v___x_347_);
v___y_269_ = v___y_334_;
v___y_270_ = v___x_349_;
v___y_271_ = v___x_352_;
v___y_272_ = v___y_335_;
v___y_273_ = v___x_351_;
v___y_274_ = v_a_345_;
v___y_275_ = v_fileName_338_;
v___y_276_ = v___y_266_;
goto v___jp_268_;
}
}
}
}
v___jp_359_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Syntax_getTailPos_x3f(v___y_362_, v___y_360_);
lean_dec(v___y_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_inc(v___y_363_);
v___y_334_ = v___y_360_;
v___y_335_ = v___y_361_;
v___y_336_ = v___y_363_;
v___y_337_ = v___y_363_;
goto v___jp_333_;
}
else
{
lean_object* v_val_365_; 
v_val_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_val_365_);
lean_dec_ref_known(v___x_364_, 1);
v___y_334_ = v___y_360_;
v___y_335_ = v___y_361_;
v___y_336_ = v___y_363_;
v___y_337_ = v_val_365_;
goto v___jp_333_;
}
}
v___jp_366_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Elab_Command_getRef___redArg(v___y_265_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v_ref_371_; lean_object* v___x_372_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v_ref_371_ = l_Lean_replaceRef(v_ref_261_, v_a_370_);
lean_dec(v_a_370_);
v___x_372_ = l_Lean_Syntax_getPos_x3f(v_ref_371_, v___y_367_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___y_360_ = v___y_367_;
v___y_361_ = v___y_368_;
v___y_362_ = v_ref_371_;
v___y_363_ = v___x_373_;
goto v___jp_359_;
}
else
{
lean_object* v_val_374_; 
v_val_374_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___x_372_, 1);
v___y_360_ = v___y_367_;
v___y_361_ = v___y_368_;
v___y_362_ = v_ref_371_;
v___y_363_ = v_val_374_;
goto v___jp_359_;
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_msgData_262_);
v_a_375_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_369_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_369_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_scopes_388_; lean_object* v___x_389_; lean_object* v_opts_390_; uint8_t v___x_391_; uint8_t v___x_392_; 
v___x_386_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_387_ = lean_st_ref_get(v___y_266_);
v_scopes_388_ = lean_ctor_get(v___x_387_, 2);
lean_inc(v_scopes_388_);
lean_dec(v___x_387_);
v___x_389_ = l_List_head_x21___redArg(v___x_386_, v_scopes_388_);
lean_dec(v_scopes_388_);
v_opts_390_ = lean_ctor_get(v___x_389_, 1);
lean_inc_ref(v_opts_390_);
lean_dec(v___x_389_);
v___x_391_ = 1;
v___x_392_ = l_Lean_instBEqMessageSeverity_beq(v_severity_263_, v___x_391_);
if (v___x_392_ == 0)
{
lean_dec_ref(v_opts_390_);
v___y_367_ = v___y_385_;
v___y_368_ = v_severity_263_;
goto v___jp_366_;
}
else
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = l_Lean_warningAsError;
v___x_394_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_390_, v___x_393_);
lean_dec_ref(v_opts_390_);
if (v___x_394_ == 0)
{
v___y_367_ = v___y_385_;
v___y_368_ = v_severity_263_;
goto v___jp_366_;
}
else
{
v___y_367_ = v___y_385_;
v___y_368_ = v___x_383_;
goto v___jp_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___boxed(lean_object* v_ref_399_, lean_object* v_msgData_400_, lean_object* v_severity_401_, lean_object* v_isSilent_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v_severity_boxed_406_; uint8_t v_isSilent_boxed_407_; lean_object* v_res_408_; 
v_severity_boxed_406_ = lean_unbox(v_severity_401_);
v_isSilent_boxed_407_ = lean_unbox(v_isSilent_402_);
v_res_408_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(v_ref_399_, v_msgData_400_, v_severity_boxed_406_, v_isSilent_boxed_407_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v_ref_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(lean_object* v_ref_409_, lean_object* v_msgData_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
uint8_t v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; 
v___x_414_ = 1;
v___x_415_ = 0;
v___x_416_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(v_ref_409_, v_msgData_410_, v___x_414_, v___x_415_, v___y_411_, v___y_412_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15___boxed(lean_object* v_ref_417_, lean_object* v_msgData_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(v_ref_417_, v_msgData_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v_ref_417_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__0));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__2));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(lean_object* v_linterOption_429_, lean_object* v_stx_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_name_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_453_; 
v_name_435_ = lean_ctor_get(v_linterOption_429_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_linterOption_429_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v_linterOption_429_, 1);
lean_dec(v_unused_454_);
v___x_437_ = v_linterOption_429_;
v_isShared_438_ = v_isSharedCheck_453_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_name_435_);
lean_dec(v_linterOption_429_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_453_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_439_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1);
lean_inc(v_name_435_);
v___x_440_ = l_Lean_MessageData_ofName(v_name_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 7);
lean_ctor_set(v___x_437_, 1, v___x_440_);
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_452_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_disable_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_443_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v_disable_445_ = l_Lean_MessageData_note(v___x_444_);
v___x_446_ = l_Lean_Linter_linterMessageTag;
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v_msg_431_);
lean_ctor_set(v___x_447_, 1, v_disable_445_);
v___x_448_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_449_, 0, v_name_435_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_inc(v_stx_430_);
v___x_450_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_450_, 0, v_stx_430_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(v_stx_430_, v___x_450_, v___y_432_, v___y_433_);
lean_dec(v_stx_430_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object* v_linterOption_455_, lean_object* v_stx_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_linterOption_455_, v_stx_456_, v_msg_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(lean_object* v_o_464_, lean_object* v_k_465_, uint8_t v_v_466_){
_start:
{
lean_object* v_map_467_; uint8_t v_hasTrace_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_482_; 
v_map_467_ = lean_ctor_get(v_o_464_, 0);
v_hasTrace_468_ = lean_ctor_get_uint8(v_o_464_, sizeof(void*)*1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_o_464_);
if (v_isSharedCheck_482_ == 0)
{
v___x_470_ = v_o_464_;
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_map_467_);
lean_dec(v_o_464_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_472_, 0, v_v_466_);
lean_inc(v_k_465_);
v___x_473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_465_, v___x_472_, v_map_467_);
if (v_hasTrace_468_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; lean_object* v___x_477_; 
v___x_474_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___closed__0));
v___x_475_ = l_Lean_Name_isPrefixOf(v___x_474_, v_k_465_);
lean_dec(v_k_465_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_477_ = v___x_470_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_473_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_475_);
return v___x_477_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_k_465_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_480_ = v___x_470_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*1, v_hasTrace_468_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___boxed(lean_object* v_o_483_, lean_object* v_k_484_, lean_object* v_v_485_){
_start:
{
uint8_t v_v_boxed_486_; lean_object* v_res_487_; 
v_v_boxed_486_ = lean_unbox(v_v_485_);
v_res_487_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(v_o_483_, v_k_484_, v_v_boxed_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object* v_opts_488_, lean_object* v_opt_489_, uint8_t v_val_490_){
_start:
{
lean_object* v_name_491_; lean_object* v___x_492_; 
v_name_491_ = lean_ctor_get(v_opt_489_, 0);
lean_inc(v_name_491_);
lean_dec_ref(v_opt_489_);
v___x_492_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(v_opts_488_, v_name_491_, v_val_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object* v_opts_493_, lean_object* v_opt_494_, lean_object* v_val_495_){
_start:
{
uint8_t v_val_boxed_496_; lean_object* v_res_497_; 
v_val_boxed_496_ = lean_unbox(v_val_495_);
v_res_497_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_opts_493_, v_opt_494_, v_val_boxed_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_498_, lean_object* v_vals_499_, lean_object* v_i_500_, lean_object* v_k_501_){
_start:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_array_get_size(v_keys_498_);
v___x_503_ = lean_nat_dec_lt(v_i_500_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v_i_500_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v_k_x27_505_; uint8_t v___x_506_; 
v_k_x27_505_ = lean_array_fget_borrowed(v_keys_498_, v_i_500_);
v___x_506_ = lean_name_eq(v_k_501_, v_k_x27_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_i_500_, v___x_507_);
lean_dec(v_i_500_);
v_i_500_ = v___x_508_;
goto _start;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_array_fget_borrowed(v_vals_499_, v_i_500_);
lean_dec(v_i_500_);
lean_inc(v___x_510_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_512_, lean_object* v_vals_513_, lean_object* v_i_514_, lean_object* v_k_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_512_, v_vals_513_, v_i_514_, v_k_515_);
lean_dec(v_k_515_);
lean_dec_ref(v_vals_513_);
lean_dec_ref(v_keys_512_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(lean_object* v_x_517_, size_t v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_es_520_; lean_object* v___x_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; 
v_es_520_ = lean_ctor_get(v_x_517_, 0);
v___x_521_ = lean_box(2);
v___x_522_ = ((size_t)31ULL);
v___x_523_ = lean_usize_land(v_x_518_, v___x_522_);
v_j_524_ = lean_usize_to_nat(v___x_523_);
v___x_525_ = lean_array_get_borrowed(v___x_521_, v_es_520_, v_j_524_);
lean_dec(v_j_524_);
switch(lean_obj_tag(v___x_525_))
{
case 0:
{
lean_object* v_key_526_; lean_object* v_val_527_; uint8_t v___x_528_; 
v_key_526_ = lean_ctor_get(v___x_525_, 0);
v_val_527_ = lean_ctor_get(v___x_525_, 1);
v___x_528_ = lean_name_eq(v_x_519_, v_key_526_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_box(0);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
lean_inc(v_val_527_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_val_527_);
return v___x_530_;
}
}
case 1:
{
lean_object* v_node_531_; size_t v___x_532_; size_t v___x_533_; 
v_node_531_ = lean_ctor_get(v___x_525_, 0);
v___x_532_ = ((size_t)5ULL);
v___x_533_ = lean_usize_shift_right(v_x_518_, v___x_532_);
v_x_517_ = v_node_531_;
v_x_518_ = v___x_533_;
goto _start;
}
default: 
{
lean_object* v___x_535_; 
v___x_535_ = lean_box(0);
return v___x_535_;
}
}
}
else
{
lean_object* v_ks_536_; lean_object* v_vs_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_ks_536_ = lean_ctor_get(v_x_517_, 0);
v_vs_537_ = lean_ctor_get(v_x_517_, 1);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_536_, v_vs_537_, v___x_538_, v_x_519_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
size_t v_x_26316__boxed_543_; lean_object* v_res_544_; 
v_x_26316__boxed_543_ = lean_unbox_usize(v_x_541_);
lean_dec(v_x_541_);
v_res_544_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_540_, v_x_26316__boxed_543_, v_x_542_);
lean_dec(v_x_542_);
lean_dec_ref(v_x_540_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
uint64_t v___y_548_; 
if (lean_obj_tag(v_x_546_) == 0)
{
uint64_t v___x_551_; 
v___x_551_ = 1723ULL;
v___y_548_ = v___x_551_;
goto v___jp_547_;
}
else
{
uint64_t v_hash_552_; 
v_hash_552_ = lean_ctor_get_uint64(v_x_546_, sizeof(void*)*2);
v___y_548_ = v_hash_552_;
goto v___jp_547_;
}
v___jp_547_:
{
size_t v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_uint64_to_usize(v___y_548_);
v___x_550_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_545_, v___x_549_, v_x_546_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg___boxed(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_x_553_, v_x_554_);
lean_dec(v_x_554_);
lean_dec_ref(v_x_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_ks_560_; lean_object* v_vs_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v_ks_560_ = lean_ctor_get(v_x_556_, 0);
v_vs_561_ = lean_ctor_get(v_x_556_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v_x_556_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_vs_561_);
lean_inc(v_ks_560_);
lean_dec(v_x_556_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_ks_560_);
v___x_566_ = lean_nat_dec_lt(v_x_557_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_x_557_);
v___x_567_ = lean_array_push(v_ks_560_, v_x_558_);
v___x_568_ = lean_array_push(v_vs_561_, v_x_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_568_);
lean_ctor_set(v___x_563_, 0, v___x_567_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v_k_x27_572_; uint8_t v___x_573_; 
v_k_x27_572_ = lean_array_fget_borrowed(v_ks_560_, v_x_557_);
v___x_573_ = lean_name_eq(v_x_558_, v_k_x27_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_575_; 
if (v_isShared_564_ == 0)
{
v___x_575_ = v___x_563_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_ks_560_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_vs_561_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_x_557_, v___x_576_);
lean_dec(v_x_557_);
v_x_556_ = v___x_575_;
v_x_557_ = v___x_577_;
goto _start;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_580_ = lean_array_fset(v_ks_560_, v_x_557_, v_x_558_);
v___x_581_ = lean_array_fset(v_vs_561_, v_x_557_, v_x_559_);
lean_dec(v_x_557_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_581_);
lean_ctor_set(v___x_563_, 0, v___x_580_);
v___x_583_ = v___x_563_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(lean_object* v_n_586_, lean_object* v_k_587_, lean_object* v_v_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(v_n_586_, v___x_589_, v_k_587_, v_v_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(lean_object* v_x_592_, size_t v_x_593_, size_t v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v_es_597_; size_t v___x_598_; size_t v___x_599_; lean_object* v_j_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_es_597_ = lean_ctor_get(v_x_592_, 0);
v___x_598_ = ((size_t)31ULL);
v___x_599_ = lean_usize_land(v_x_593_, v___x_598_);
v_j_600_ = lean_usize_to_nat(v___x_599_);
v___x_601_ = lean_array_get_size(v_es_597_);
v___x_602_ = lean_nat_dec_lt(v_j_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v_j_600_);
lean_dec(v_x_596_);
lean_dec(v_x_595_);
return v_x_592_;
}
else
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_641_; 
lean_inc_ref(v_es_597_);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_x_592_, 0);
lean_dec(v_unused_642_);
v___x_604_ = v_x_592_;
v_isShared_605_ = v_isSharedCheck_641_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_x_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_641_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_v_606_; lean_object* v___x_607_; lean_object* v_xs_x27_608_; lean_object* v___y_610_; 
v_v_606_ = lean_array_fget(v_es_597_, v_j_600_);
v___x_607_ = lean_box(0);
v_xs_x27_608_ = lean_array_fset(v_es_597_, v_j_600_, v___x_607_);
switch(lean_obj_tag(v_v_606_))
{
case 0:
{
lean_object* v_key_615_; lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_key_615_ = lean_ctor_get(v_v_606_, 0);
v_val_616_ = lean_ctor_get(v_v_606_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_v_606_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v_v_606_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_inc(v_key_615_);
lean_dec(v_v_606_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = lean_name_eq(v_x_595_, v_key_615_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_del_object(v___x_618_);
v___x_621_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_615_, v_val_616_, v_x_595_, v_x_596_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___y_610_ = v___x_622_;
goto v___jp_609_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v_val_616_);
lean_dec(v_key_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v_x_596_);
lean_ctor_set(v___x_618_, 0, v_x_595_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_x_595_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_x_596_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v___y_610_ = v___x_624_;
goto v___jp_609_;
}
}
}
}
case 1:
{
lean_object* v_node_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_639_; 
v_node_627_ = lean_ctor_get(v_v_606_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_v_606_);
if (v_isSharedCheck_639_ == 0)
{
v___x_629_ = v_v_606_;
v_isShared_630_ = v_isSharedCheck_639_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_node_627_);
lean_dec(v_v_606_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_639_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_631_ = ((size_t)5ULL);
v___x_632_ = lean_usize_shift_right(v_x_593_, v___x_631_);
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_x_594_, v___x_633_);
v___x_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_node_627_, v___x_632_, v___x_634_, v_x_595_, v_x_596_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_635_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v___y_610_ = v___x_637_;
goto v___jp_609_;
}
}
}
default: 
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_x_595_);
lean_ctor_set(v___x_640_, 1, v_x_596_);
v___y_610_ = v___x_640_;
goto v___jp_609_;
}
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_array_fset(v_xs_x27_608_, v_j_600_, v___y_610_);
lean_dec(v_j_600_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_611_);
v___x_613_ = v___x_604_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
else
{
lean_object* v_ks_643_; lean_object* v_vs_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_662_; 
v_ks_643_ = lean_ctor_get(v_x_592_, 0);
v_vs_644_ = lean_ctor_get(v_x_592_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_662_ == 0)
{
v___x_646_ = v_x_592_;
v_isShared_647_ = v_isSharedCheck_662_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_vs_644_);
lean_inc(v_ks_643_);
lean_dec(v_x_592_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_662_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_ks_643_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_vs_644_);
v___x_649_ = v_reuseFailAlloc_661_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v_newNode_650_; size_t v___x_651_; uint8_t v___x_652_; 
v_newNode_650_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(v___x_649_, v_x_595_, v_x_596_);
v___x_651_ = ((size_t)7ULL);
v___x_652_ = lean_usize_dec_le(v___x_651_, v_x_594_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_650_);
v___x_654_ = lean_unsigned_to_nat(4u);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
if (v___x_655_ == 0)
{
lean_object* v_ks_656_; lean_object* v_vs_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_ks_656_ = lean_ctor_get(v_newNode_650_, 0);
lean_inc_ref(v_ks_656_);
v_vs_657_ = lean_ctor_get(v_newNode_650_, 1);
lean_inc_ref(v_vs_657_);
lean_dec_ref(v_newNode_650_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0);
v___x_660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_x_594_, v_ks_656_, v_vs_657_, v___x_658_, v___x_659_);
lean_dec_ref(v_vs_657_);
lean_dec_ref(v_ks_656_);
return v___x_660_;
}
else
{
return v_newNode_650_;
}
}
else
{
return v_newNode_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(size_t v_depth_663_, lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_i_666_, lean_object* v_entries_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_keys_664_);
v___x_669_ = lean_nat_dec_lt(v_i_666_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_i_666_);
return v_entries_667_;
}
else
{
lean_object* v_k_670_; lean_object* v_v_671_; uint64_t v___y_673_; 
v_k_670_ = lean_array_fget_borrowed(v_keys_664_, v_i_666_);
v_v_671_ = lean_array_fget_borrowed(v_vals_665_, v_i_666_);
if (lean_obj_tag(v_k_670_) == 0)
{
uint64_t v___x_684_; 
v___x_684_ = 1723ULL;
v___y_673_ = v___x_684_;
goto v___jp_672_;
}
else
{
uint64_t v_hash_685_; 
v_hash_685_ = lean_ctor_get_uint64(v_k_670_, sizeof(void*)*2);
v___y_673_ = v_hash_685_;
goto v___jp_672_;
}
v___jp_672_:
{
size_t v_h_674_; size_t v___x_675_; lean_object* v___x_676_; size_t v___x_677_; size_t v___x_678_; size_t v___x_679_; size_t v_h_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_h_674_ = lean_uint64_to_usize(v___y_673_);
v___x_675_ = ((size_t)5ULL);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_sub(v_depth_663_, v___x_677_);
v___x_679_ = lean_usize_mul(v___x_675_, v___x_678_);
v_h_680_ = lean_usize_shift_right(v_h_674_, v___x_679_);
v___x_681_ = lean_nat_add(v_i_666_, v___x_676_);
lean_dec(v_i_666_);
lean_inc(v_v_671_);
lean_inc(v_k_670_);
v___x_682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_entries_667_, v_h_680_, v_depth_663_, v_k_670_, v_v_671_);
v_i_666_ = v___x_681_;
v_entries_667_ = v___x_682_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg___boxed(lean_object* v_depth_686_, lean_object* v_keys_687_, lean_object* v_vals_688_, lean_object* v_i_689_, lean_object* v_entries_690_){
_start:
{
size_t v_depth_boxed_691_; lean_object* v_res_692_; 
v_depth_boxed_691_ = lean_unbox_usize(v_depth_686_);
lean_dec(v_depth_686_);
v_res_692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_depth_boxed_691_, v_keys_687_, v_vals_688_, v_i_689_, v_entries_690_);
lean_dec_ref(v_vals_688_);
lean_dec_ref(v_keys_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
size_t v_x_26457__boxed_698_; size_t v_x_26458__boxed_699_; lean_object* v_res_700_; 
v_x_26457__boxed_698_ = lean_unbox_usize(v_x_694_);
lean_dec(v_x_694_);
v_x_26458__boxed_699_ = lean_unbox_usize(v_x_695_);
lean_dec(v_x_695_);
v_res_700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_693_, v_x_26457__boxed_698_, v_x_26458__boxed_699_, v_x_696_, v_x_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
uint64_t v___y_705_; 
if (lean_obj_tag(v_x_702_) == 0)
{
uint64_t v___x_709_; 
v___x_709_ = 1723ULL;
v___y_705_ = v___x_709_;
goto v___jp_704_;
}
else
{
uint64_t v_hash_710_; 
v_hash_710_ = lean_ctor_get_uint64(v_x_702_, sizeof(void*)*2);
v___y_705_ = v_hash_710_;
goto v___jp_704_;
}
v___jp_704_:
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_uint64_to_usize(v___y_705_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_701_, v___x_706_, v___x_707_, v_x_702_, v_x_703_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(lean_object* v_oldCounters_711_, lean_object* v_x_712_, lean_object* v_____s_713_){
_start:
{
lean_object* v_fst_714_; lean_object* v_snd_715_; lean_object* v___x_716_; 
v_fst_714_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_fst_714_);
v_snd_715_ = lean_ctor_get(v_x_712_, 1);
lean_inc(v_snd_715_);
lean_dec_ref(v_x_712_);
v___x_716_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_oldCounters_711_, v_fst_714_);
if (lean_obj_tag(v___x_716_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_val_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v_result_722_; lean_object* v___x_724_; 
v___x_721_ = lean_nat_sub(v_snd_715_, v_val_717_);
lean_dec(v_val_717_);
lean_dec(v_snd_715_);
v_result_722_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_____s_713_, v_fst_714_, v___x_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_result_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_result_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_result_727_; lean_object* v___x_728_; 
lean_dec(v___x_716_);
v_result_727_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_____s_713_, v_fst_714_, v_snd_715_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_result_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed(lean_object* v_oldCounters_729_, lean_object* v_x_730_, lean_object* v_____s_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(v_oldCounters_729_, v_x_730_, v_____s_731_);
lean_dec_ref(v_oldCounters_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0(lean_object* v_f_733_, lean_object* v_s_734_, lean_object* v_a_735_, lean_object* v_b_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_a_735_);
lean_ctor_set(v___x_737_, 1, v_b_736_);
v___x_738_ = lean_apply_2(v_f_733_, v___x_737_, v_s_734_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_738_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_738_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(lean_object* v_f_755_, lean_object* v_keys_756_, lean_object* v_vals_757_, lean_object* v_i_758_, lean_object* v_acc_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_array_get_size(v_keys_756_);
v___x_761_ = lean_nat_dec_lt(v_i_758_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_i_758_);
lean_dec_ref(v_f_755_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_acc_759_);
return v___x_762_;
}
else
{
lean_object* v_k_763_; lean_object* v_v_764_; lean_object* v___x_765_; 
v_k_763_ = lean_array_fget_borrowed(v_keys_756_, v_i_758_);
v_v_764_ = lean_array_fget_borrowed(v_vals_757_, v_i_758_);
lean_inc_ref(v_f_755_);
lean_inc(v_v_764_);
lean_inc(v_k_763_);
v___x_765_ = lean_apply_3(v_f_755_, v_acc_759_, v_k_763_, v_v_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec(v_i_758_);
lean_dec_ref(v_f_755_);
return v___x_765_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_i_758_, v___x_767_);
lean_dec(v_i_758_);
v_i_758_ = v___x_768_;
v_acc_759_ = v_a_766_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg___boxed(lean_object* v_f_770_, lean_object* v_keys_771_, lean_object* v_vals_772_, lean_object* v_i_773_, lean_object* v_acc_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_770_, v_keys_771_, v_vals_772_, v_i_773_, v_acc_774_);
lean_dec_ref(v_vals_772_);
lean_dec_ref(v_keys_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(lean_object* v_f_776_, lean_object* v_as_777_, size_t v_i_778_, size_t v_stop_779_, lean_object* v_b_780_){
_start:
{
lean_object* v_a_782_; lean_object* v___y_787_; uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_eq(v_i_778_, v_stop_779_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_array_uget_borrowed(v_as_777_, v_i_778_);
switch(lean_obj_tag(v___x_790_))
{
case 0:
{
lean_object* v_key_791_; lean_object* v_val_792_; lean_object* v___x_793_; 
v_key_791_ = lean_ctor_get(v___x_790_, 0);
v_val_792_ = lean_ctor_get(v___x_790_, 1);
lean_inc_ref(v_f_776_);
lean_inc(v_val_792_);
lean_inc(v_key_791_);
v___x_793_ = lean_apply_3(v_f_776_, v_b_780_, v_key_791_, v_val_792_);
v___y_787_ = v___x_793_;
goto v___jp_786_;
}
case 1:
{
lean_object* v_node_794_; lean_object* v___x_795_; 
v_node_794_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_node_794_);
lean_inc_ref(v_f_776_);
v___x_795_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_776_, v_node_794_, v_b_780_);
v___y_787_ = v___x_795_;
goto v___jp_786_;
}
default: 
{
v_a_782_ = v_b_780_;
goto v___jp_781_;
}
}
}
else
{
lean_object* v___x_796_; 
lean_dec_ref(v_f_776_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_b_780_);
return v___x_796_;
}
v___jp_781_:
{
size_t v___x_783_; size_t v___x_784_; 
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_778_, v___x_783_);
v_i_778_ = v___x_784_;
v_b_780_ = v_a_782_;
goto _start;
}
v___jp_786_:
{
if (lean_obj_tag(v___y_787_) == 0)
{
lean_dec_ref(v_f_776_);
return v___y_787_;
}
else
{
lean_object* v_a_788_; 
v_a_788_ = lean_ctor_get(v___y_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___y_787_, 1);
v_a_782_ = v_a_788_;
goto v___jp_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(lean_object* v_f_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v_es_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_813_; 
v_es_800_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_813_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_813_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_es_800_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_813_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v_es_800_);
v___x_806_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_es_800_);
lean_dec_ref(v_f_797_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 1);
lean_ctor_set(v___x_802_, 0, v_x_799_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_x_799_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
lean_del_object(v___x_802_);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_805_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_797_, v_es_800_, v___x_810_, v___x_811_, v_x_799_);
lean_dec_ref(v_es_800_);
return v___x_812_;
}
}
}
else
{
lean_object* v_ks_814_; lean_object* v_vs_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_ks_814_ = lean_ctor_get(v_x_798_, 0);
lean_inc_ref(v_ks_814_);
v_vs_815_ = lean_ctor_get(v_x_798_, 1);
lean_inc_ref(v_vs_815_);
lean_dec_ref_known(v_x_798_, 2);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_797_, v_ks_814_, v_vs_815_, v___x_816_, v_x_799_);
lean_dec_ref(v_vs_815_);
lean_dec_ref(v_ks_814_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg___boxed(lean_object* v_f_818_, lean_object* v_as_819_, lean_object* v_i_820_, lean_object* v_stop_821_, lean_object* v_b_822_){
_start:
{
size_t v_i_boxed_823_; size_t v_stop_boxed_824_; lean_object* v_res_825_; 
v_i_boxed_823_ = lean_unbox_usize(v_i_820_);
lean_dec(v_i_820_);
v_stop_boxed_824_ = lean_unbox_usize(v_stop_821_);
lean_dec(v_stop_821_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_818_, v_as_819_, v_i_boxed_823_, v_stop_boxed_824_, v_b_822_);
lean_dec_ref(v_as_819_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(lean_object* v_map_826_, lean_object* v_init_827_, lean_object* v_f_828_){
_start:
{
lean_object* v___f_829_; lean_object* v___x_830_; lean_object* v_a_831_; 
v___f_829_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0), 4, 1);
lean_closure_set(v___f_829_, 0, v_f_828_);
lean_inc_ref(v_map_826_);
v___x_830_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v___f_829_, v_map_826_, v_init_827_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
return v_a_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___boxed(lean_object* v_map_832_, lean_object* v_init_833_, lean_object* v_f_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_map_832_, v_init_833_, v_f_834_);
lean_dec_ref(v_map_832_);
return v_res_835_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0(void){
_start:
{
lean_object* v___x_836_; lean_object* v_result_837_; 
v___x_836_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v_result_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_result_837_, 0, v___x_836_);
return v_result_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object* v_newCounters_838_, lean_object* v_oldCounters_839_){
_start:
{
lean_object* v___f_840_; lean_object* v_result_841_; lean_object* v___x_842_; 
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed), 3, 1);
lean_closure_set(v___f_840_, 0, v_oldCounters_839_);
v_result_841_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0);
v___x_842_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_newCounters_838_, v_result_841_, v___f_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object* v_newCounters_843_, lean_object* v_oldCounters_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_newCounters_843_, v_oldCounters_844_);
lean_dec_ref(v_newCounters_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object* v___x_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
if (lean_obj_tag(v_a_847_) == 0)
{
lean_object* v___x_849_; 
lean_dec_ref(v___x_846_);
v___x_849_ = lean_array_to_list(v_a_848_);
return v___x_849_;
}
else
{
lean_object* v_head_850_; lean_object* v_tail_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_head_850_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_head_850_);
v_tail_851_ = lean_ctor_get(v_a_847_, 1);
lean_inc(v_tail_851_);
lean_dec_ref_known(v_a_847_, 2);
v_fst_852_ = lean_ctor_get(v_head_850_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v_head_850_, 1);
lean_inc(v_snd_853_);
lean_dec(v_head_850_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_nat_dec_lt(v___x_854_, v_snd_853_);
lean_dec(v_snd_853_);
if (v___x_855_ == 0)
{
lean_dec(v_fst_852_);
v_a_847_ = v_tail_851_;
goto _start;
}
else
{
uint8_t v___x_857_; 
lean_inc(v_fst_852_);
lean_inc_ref(v___x_846_);
v___x_857_ = l_Lean_getReducibilityStatusCore(v___x_846_, v_fst_852_);
if (v___x_857_ == 1)
{
uint8_t v___x_858_; 
lean_inc_ref(v___x_846_);
v___x_858_ = l_Lean_Meta_isInstanceCore(v___x_846_, v_fst_852_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = l_Lean_MessageData_ofConstName(v_fst_852_, v___x_858_);
v___x_860_ = lean_array_push(v_a_848_, v___x_859_);
v_a_847_ = v_tail_851_;
v_a_848_ = v___x_860_;
goto _start;
}
else
{
lean_dec(v_fst_852_);
v_a_847_ = v_tail_851_;
goto _start;
}
}
else
{
lean_dec(v_fst_852_);
v_a_847_ = v_tail_851_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0(lean_object* v_f_864_, lean_object* v_x1_865_, lean_object* v_x2_866_, lean_object* v_x3_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = lean_apply_3(v_f_864_, v_x1_865_, v_x2_866_, v_x3_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(lean_object* v_f_869_, lean_object* v_keys_870_, lean_object* v_vals_871_, lean_object* v_i_872_, lean_object* v_acc_873_){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_array_get_size(v_keys_870_);
v___x_875_ = lean_nat_dec_lt(v_i_872_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec(v_i_872_);
lean_dec(v_f_869_);
return v_acc_873_;
}
else
{
lean_object* v_k_876_; lean_object* v_v_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_k_876_ = lean_array_fget_borrowed(v_keys_870_, v_i_872_);
v_v_877_ = lean_array_fget_borrowed(v_vals_871_, v_i_872_);
lean_inc(v_f_869_);
lean_inc(v_v_877_);
lean_inc(v_k_876_);
v___x_878_ = lean_apply_3(v_f_869_, v_acc_873_, v_k_876_, v_v_877_);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_i_872_, v___x_879_);
lean_dec(v_i_872_);
v_i_872_ = v___x_880_;
v_acc_873_ = v___x_878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg___boxed(lean_object* v_f_882_, lean_object* v_keys_883_, lean_object* v_vals_884_, lean_object* v_i_885_, lean_object* v_acc_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_882_, v_keys_883_, v_vals_884_, v_i_885_, v_acc_886_);
lean_dec_ref(v_vals_884_);
lean_dec_ref(v_keys_883_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(lean_object* v_f_888_, lean_object* v_as_889_, size_t v_i_890_, size_t v_stop_891_, lean_object* v_b_892_){
_start:
{
lean_object* v___y_894_; uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_eq(v_i_890_, v_stop_891_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_array_uget_borrowed(v_as_889_, v_i_890_);
switch(lean_obj_tag(v___x_899_))
{
case 0:
{
lean_object* v_key_900_; lean_object* v_val_901_; lean_object* v___x_902_; 
v_key_900_ = lean_ctor_get(v___x_899_, 0);
v_val_901_ = lean_ctor_get(v___x_899_, 1);
lean_inc(v_f_888_);
lean_inc(v_val_901_);
lean_inc(v_key_900_);
v___x_902_ = lean_apply_3(v_f_888_, v_b_892_, v_key_900_, v_val_901_);
v___y_894_ = v___x_902_;
goto v___jp_893_;
}
case 1:
{
lean_object* v_node_903_; lean_object* v___x_904_; 
v_node_903_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_f_888_);
v___x_904_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_888_, v_node_903_, v_b_892_);
v___y_894_ = v___x_904_;
goto v___jp_893_;
}
default: 
{
v___y_894_ = v_b_892_;
goto v___jp_893_;
}
}
}
else
{
lean_dec(v_f_888_);
return v_b_892_;
}
v___jp_893_:
{
size_t v___x_895_; size_t v___x_896_; 
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_890_, v___x_895_);
v_i_890_ = v___x_896_;
v_b_892_ = v___y_894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(lean_object* v_f_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v_es_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_es_908_ = lean_ctor_get(v_x_906_, 0);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_es_908_);
v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec(v_f_905_);
return v_x_907_;
}
else
{
size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; 
v___x_912_ = ((size_t)0ULL);
v___x_913_ = lean_usize_of_nat(v___x_910_);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_905_, v_es_908_, v___x_912_, v___x_913_, v_x_907_);
return v___x_914_;
}
}
else
{
lean_object* v_ks_915_; lean_object* v_vs_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_ks_915_ = lean_ctor_get(v_x_906_, 0);
v_vs_916_ = lean_ctor_get(v_x_906_, 1);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_905_, v_ks_915_, v_vs_916_, v___x_917_, v_x_907_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg___boxed(lean_object* v_f_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_919_, v_x_920_, v_x_921_);
lean_dec_ref(v_x_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg___boxed(lean_object* v_f_923_, lean_object* v_as_924_, lean_object* v_i_925_, lean_object* v_stop_926_, lean_object* v_b_927_){
_start:
{
size_t v_i_boxed_928_; size_t v_stop_boxed_929_; lean_object* v_res_930_; 
v_i_boxed_928_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_stop_boxed_929_ = lean_unbox_usize(v_stop_926_);
lean_dec(v_stop_926_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_923_, v_as_924_, v_i_boxed_928_, v_stop_boxed_929_, v_b_927_);
lean_dec_ref(v_as_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(lean_object* v_map_931_, lean_object* v_f_932_, lean_object* v_init_933_){
_start:
{
lean_object* v___f_934_; lean_object* v___x_935_; 
v___f_934_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0), 4, 1);
lean_closure_set(v___f_934_, 0, v_f_932_);
v___x_935_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v___f_934_, v_map_931_, v_init_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___boxed(lean_object* v_map_936_, lean_object* v_f_937_, lean_object* v_init_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_map_936_, v_f_937_, v_init_938_);
lean_dec_ref(v_map_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___lam__0(lean_object* v_ps_940_, lean_object* v_k_941_, lean_object* v_v_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_k_941_);
lean_ctor_set(v___x_943_, 1, v_v_942_);
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_ps_940_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(lean_object* v_m_946_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___f_947_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___closed__0));
v___x_948_ = lean_box(0);
v___x_949_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_m_946_, v___f_947_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___boxed(lean_object* v_m_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v_m_950_);
lean_dec_ref(v_m_950_);
return v_res_951_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__0));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__2));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_box(1);
v___x_959_ = l_Lean_MessageData_ofFormat(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__5));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__9));
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__12));
v___x_973_ = l_Lean_MessageData_ofFormat(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(lean_object* v_kind_978_, lean_object* v_a_979_, uint8_t v___x_980_, lean_object* v_diag_981_, lean_object* v___x_982_, uint8_t v_a_983_, uint8_t v_val_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; uint16_t v___y_1012_; lean_object* v___y_1013_; lean_object* v_fileName_1014_; lean_object* v_fileMap_1015_; lean_object* v_currNamespace_1016_; lean_object* v_openDecls_1017_; lean_object* v_initHeartbeats_1018_; lean_object* v_maxHeartbeats_1019_; lean_object* v_quotContext_1020_; lean_object* v_currMacroScope_1021_; lean_object* v_cancelTk_x3f_1022_; lean_object* v_inheritedTraceOptions_1023_; lean_object* v_currRecDepth_1024_; lean_object* v_ref_1025_; uint8_t v_suppressElabErrors_1026_; uint8_t v_isRecordingDeps_1027_; lean_object* v___y_1028_; lean_object* v_toCold_1110_; lean_object* v_currRecDepth_1111_; lean_object* v_ref_1112_; uint8_t v_suppressElabErrors_1113_; uint8_t v_isRecordingDeps_1114_; lean_object* v_fileName_1115_; lean_object* v_fileMap_1116_; lean_object* v_options_1117_; lean_object* v_currNamespace_1118_; lean_object* v_openDecls_1119_; lean_object* v_initHeartbeats_1120_; lean_object* v_maxHeartbeats_1121_; lean_object* v_quotContext_1122_; lean_object* v_currMacroScope_1123_; lean_object* v_cancelTk_x3f_1124_; lean_object* v_inheritedTraceOptions_1125_; uint8_t v___y_1127_; uint16_t v___y_1128_; lean_object* v___y_1129_; uint8_t v___y_1152_; uint16_t v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; uint16_t v___y_1157_; uint8_t v___y_1158_; lean_object* v___y_1159_; uint8_t v___y_1160_; lean_object* v___y_1162_; 
v_toCold_1110_ = lean_ctor_get(v___y_987_, 0);
v_currRecDepth_1111_ = lean_ctor_get(v___y_987_, 1);
v_ref_1112_ = lean_ctor_get(v___y_987_, 2);
v_suppressElabErrors_1113_ = lean_ctor_get_uint8(v___y_987_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1114_ = lean_ctor_get_uint8(v___y_987_, sizeof(void*)*3 + 3);
v_fileName_1115_ = lean_ctor_get(v_toCold_1110_, 0);
v_fileMap_1116_ = lean_ctor_get(v_toCold_1110_, 1);
v_options_1117_ = lean_ctor_get(v_toCold_1110_, 2);
v_currNamespace_1118_ = lean_ctor_get(v_toCold_1110_, 4);
v_openDecls_1119_ = lean_ctor_get(v_toCold_1110_, 5);
v_initHeartbeats_1120_ = lean_ctor_get(v_toCold_1110_, 6);
v_maxHeartbeats_1121_ = lean_ctor_get(v_toCold_1110_, 7);
v_quotContext_1122_ = lean_ctor_get(v_toCold_1110_, 8);
v_currMacroScope_1123_ = lean_ctor_get(v_toCold_1110_, 9);
v_cancelTk_x3f_1124_ = lean_ctor_get(v_toCold_1110_, 10);
v_inheritedTraceOptions_1125_ = lean_ctor_get(v_toCold_1110_, 11);
if (v_isRecordingDeps_1114_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1117_);
v___x_1172_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_options_1117_, v___x_1171_, v_a_983_);
v___y_1162_ = v___x_1172_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1173_; 
lean_inc_ref(v_options_1117_);
v___x_1173_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1117_);
v___y_1162_ = v___x_1173_;
goto v___jp_1161_;
}
v___jp_990_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_994_ = l_Lean_stringToMessageData(v_kind_978_);
v___x_995_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_inc_ref(v___y_993_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___y_993_);
v___x_998_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4);
v___x_1001_ = l_Lean_MessageData_joinSep(v___y_991_, v___x_1000_);
v___x_1002_ = l_Lean_indentD(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_999_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_Exception_toMessageData(v___y_992_);
v___x_1007_ = l_Lean_indentD(v___x_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1005_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
v___jp_1011_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1029_ = l_Lean_maxRecDepth;
v___x_1030_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v___y_1013_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1031_, 0, v_fileName_1014_);
lean_ctor_set(v___x_1031_, 1, v_fileMap_1015_);
lean_ctor_set(v___x_1031_, 2, v___y_1013_);
lean_ctor_set(v___x_1031_, 3, v___x_1030_);
lean_ctor_set(v___x_1031_, 4, v_currNamespace_1016_);
lean_ctor_set(v___x_1031_, 5, v_openDecls_1017_);
lean_ctor_set(v___x_1031_, 6, v_initHeartbeats_1018_);
lean_ctor_set(v___x_1031_, 7, v_maxHeartbeats_1019_);
lean_ctor_set(v___x_1031_, 8, v_quotContext_1020_);
lean_ctor_set(v___x_1031_, 9, v_currMacroScope_1021_);
lean_ctor_set(v___x_1031_, 10, v_cancelTk_x3f_1022_);
lean_ctor_set(v___x_1031_, 11, v_inheritedTraceOptions_1023_);
lean_inc(v_ref_1025_);
lean_inc(v_currRecDepth_1024_);
v___x_1032_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v_currRecDepth_1024_);
lean_ctor_set(v___x_1032_, 2, v_ref_1025_);
lean_ctor_set_uint16(v___x_1032_, sizeof(void*)*3, v___y_1012_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*3 + 2, v_suppressElabErrors_1026_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*3 + 3, v_isRecordingDeps_1027_);
lean_inc_ref(v_a_979_);
v___x_1033_ = l_Lean_Meta_check(v_a_979_, v___x_980_, v___y_985_, v___y_986_, v___x_1032_, v___y_1028_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v_diag_1035_; lean_object* v_unfoldCounter_1036_; lean_object* v___x_1037_; lean_object* v_mctx_1038_; lean_object* v_cache_1039_; lean_object* v_zetaDeltaFVarIds_1040_; lean_object* v_postponed_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref_known(v___x_1033_, 1);
v___x_1034_ = lean_st_ref_get(v___y_986_);
v_diag_1035_ = lean_ctor_get(v___x_1034_, 4);
lean_inc_ref(v_diag_1035_);
lean_dec(v___x_1034_);
v_unfoldCounter_1036_ = lean_ctor_get(v_diag_1035_, 0);
lean_inc_ref(v_unfoldCounter_1036_);
lean_dec_ref(v_diag_1035_);
v___x_1037_ = lean_st_ref_take(v___y_986_);
v_mctx_1038_ = lean_ctor_get(v___x_1037_, 0);
v_cache_1039_ = lean_ctor_get(v___x_1037_, 1);
v_zetaDeltaFVarIds_1040_ = lean_ctor_get(v___x_1037_, 2);
v_postponed_1041_ = lean_ctor_get(v___x_1037_, 3);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1037_, 4);
lean_dec(v_unused_1092_);
v___x_1043_ = v___x_1037_;
v_isShared_1044_ = v_isSharedCheck_1091_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_postponed_1041_);
lean_inc(v_zetaDeltaFVarIds_1040_);
lean_inc(v_cache_1039_);
lean_inc(v_mctx_1038_);
lean_dec(v___x_1037_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1091_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 4, v_diag_981_);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_mctx_1038_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_cache_1039_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_zetaDeltaFVarIds_1040_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_postponed_1041_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_diag_981_);
v___x_1046_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_st_ref_put(v___y_986_, v___x_1046_);
v___x_1048_ = 5;
v___x_1049_ = l_Lean_Meta_check(v_a_979_, v___x_1048_, v___y_985_, v___y_986_, v___x_1032_, v___y_1028_);
lean_dec_ref_known(v___x_1032_, 3);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_unfoldCounter_1036_);
lean_dec_ref(v_kind_978_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1049_, 0);
lean_dec(v_unused_1058_);
v___x_1051_ = v___x_1049_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v___x_1049_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = lean_box(0);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1089_; 
v_a_1059_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1061_ = v___x_1049_;
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1049_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Lean_Exception_isInterrupt(v_a_1059_);
if (v___x_1063_ == 0)
{
uint8_t v___x_1064_; 
lean_inc(v_a_1059_);
v___x_1064_ = l_Lean_Exception_isRuntime(v_a_1059_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v_diag_1066_; lean_object* v_unfoldCounter_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_env_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1065_ = lean_st_ref_get(v___y_986_);
v_diag_1066_ = lean_ctor_get(v___x_1065_, 4);
lean_inc_ref(v_diag_1066_);
lean_dec(v___x_1065_);
v_unfoldCounter_1067_ = lean_ctor_get(v_diag_1066_, 0);
lean_inc_ref(v_unfoldCounter_1067_);
lean_dec_ref(v_diag_1066_);
v___x_1068_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_unfoldCounter_1036_, v_unfoldCounter_1067_);
lean_dec_ref(v_unfoldCounter_1036_);
v___x_1069_ = lean_st_ref_get(v___y_1028_);
v_env_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc_ref(v_env_1070_);
lean_dec(v___x_1069_);
v___x_1071_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_982_);
v___x_1073_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_env_1070_, v___x_1071_, v___x_1072_);
v___x_1074_ = l_List_isEmpty___redArg(v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
lean_del_object(v___x_1061_);
v___x_1075_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7));
v___x_1076_ = lean_string_dec_eq(v_kind_978_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10);
v___y_991_ = v___x_1073_;
v___y_992_ = v_a_1059_;
v___y_993_ = v___x_1077_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13);
v___y_991_ = v___x_1073_;
v___y_992_ = v_a_1059_;
v___y_993_ = v___x_1078_;
goto v___jp_990_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec(v___x_1073_);
lean_dec(v_a_1059_);
lean_dec_ref(v_kind_978_);
v___x_1079_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1079_);
v___x_1081_ = v___x_1061_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v___x_1084_; 
lean_dec_ref(v_unfoldCounter_1036_);
lean_dec_ref(v_kind_978_);
if (v_isShared_1062_ == 0)
{
v___x_1084_ = v___x_1061_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1059_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v___x_1087_; 
lean_dec_ref(v_unfoldCounter_1036_);
lean_dec_ref(v_kind_978_);
if (v_isShared_1062_ == 0)
{
v___x_1087_ = v___x_1061_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1059_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref_known(v___x_1032_, 3);
lean_dec_ref(v_diag_981_);
lean_dec_ref(v_a_979_);
lean_dec_ref(v_kind_978_);
v_a_1093_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1095_ = v___x_1033_;
v_isShared_1096_ = v_isSharedCheck_1109_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1033_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1109_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_Exception_isInterrupt(v_a_1093_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
lean_inc(v_a_1093_);
v___x_1098_ = l_Lean_Exception_isRuntime(v_a_1093_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_dec(v_a_1093_);
v___x_1099_ = lean_box(0);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1099_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v___x_1104_; 
if (v_isShared_1096_ == 0)
{
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1093_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v___x_1107_; 
if (v_isShared_1096_ == 0)
{
v___x_1107_ = v___x_1095_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1093_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
v___jp_1126_:
{
lean_object* v___x_1130_; lean_object* v_env_1131_; lean_object* v_nextMacroScope_1132_; lean_object* v_ngen_1133_; lean_object* v_auxDeclNGen_1134_; lean_object* v_traceState_1135_; lean_object* v_recordedDeps_1136_; lean_object* v_messages_1137_; lean_object* v_infoState_1138_; lean_object* v_snapshotTasks_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1149_; 
v___x_1130_ = lean_st_ref_take(v___y_988_);
v_env_1131_ = lean_ctor_get(v___x_1130_, 0);
v_nextMacroScope_1132_ = lean_ctor_get(v___x_1130_, 1);
v_ngen_1133_ = lean_ctor_get(v___x_1130_, 2);
v_auxDeclNGen_1134_ = lean_ctor_get(v___x_1130_, 3);
v_traceState_1135_ = lean_ctor_get(v___x_1130_, 4);
v_recordedDeps_1136_ = lean_ctor_get(v___x_1130_, 6);
v_messages_1137_ = lean_ctor_get(v___x_1130_, 7);
v_infoState_1138_ = lean_ctor_get(v___x_1130_, 8);
v_snapshotTasks_1139_ = lean_ctor_get(v___x_1130_, 9);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v___x_1130_, 5);
lean_dec(v_unused_1150_);
v___x_1141_ = v___x_1130_;
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snapshotTasks_1139_);
lean_inc(v_infoState_1138_);
lean_inc(v_messages_1137_);
lean_inc(v_recordedDeps_1136_);
lean_inc(v_traceState_1135_);
lean_inc(v_auxDeclNGen_1134_);
lean_inc(v_ngen_1133_);
lean_inc(v_nextMacroScope_1132_);
lean_inc(v_env_1131_);
lean_dec(v___x_1130_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1143_ = l_Lean_Kernel_enableDiag(v_env_1131_, v___y_1127_);
v___x_1144_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 5, v___x_1144_);
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_nextMacroScope_1132_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_ngen_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_auxDeclNGen_1134_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_traceState_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 6, v_recordedDeps_1136_);
lean_ctor_set(v_reuseFailAlloc_1148_, 7, v_messages_1137_);
lean_ctor_set(v_reuseFailAlloc_1148_, 8, v_infoState_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 9, v_snapshotTasks_1139_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_st_ref_put(v___y_988_, v___x_1146_);
lean_inc_ref(v_inheritedTraceOptions_1125_);
lean_inc(v_cancelTk_x3f_1124_);
lean_inc(v_currMacroScope_1123_);
lean_inc(v_quotContext_1122_);
lean_inc(v_maxHeartbeats_1121_);
lean_inc(v_initHeartbeats_1120_);
lean_inc(v_openDecls_1119_);
lean_inc(v_currNamespace_1118_);
lean_inc_ref(v_fileMap_1116_);
lean_inc_ref(v_fileName_1115_);
v___y_1012_ = v___y_1128_;
v___y_1013_ = v___y_1129_;
v_fileName_1014_ = v_fileName_1115_;
v_fileMap_1015_ = v_fileMap_1116_;
v_currNamespace_1016_ = v_currNamespace_1118_;
v_openDecls_1017_ = v_openDecls_1119_;
v_initHeartbeats_1018_ = v_initHeartbeats_1120_;
v_maxHeartbeats_1019_ = v_maxHeartbeats_1121_;
v_quotContext_1020_ = v_quotContext_1122_;
v_currMacroScope_1021_ = v_currMacroScope_1123_;
v_cancelTk_x3f_1022_ = v_cancelTk_x3f_1124_;
v_inheritedTraceOptions_1023_ = v_inheritedTraceOptions_1125_;
v_currRecDepth_1024_ = v_currRecDepth_1111_;
v_ref_1025_ = v_ref_1112_;
v_suppressElabErrors_1026_ = v_suppressElabErrors_1113_;
v_isRecordingDeps_1027_ = v_isRecordingDeps_1114_;
v___y_1028_ = v___y_988_;
goto v___jp_1011_;
}
}
}
v___jp_1151_:
{
if (v___y_1155_ == 0)
{
v___y_1127_ = v___y_1152_;
v___y_1128_ = v___y_1153_;
v___y_1129_ = v___y_1154_;
goto v___jp_1126_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1125_);
lean_inc(v_cancelTk_x3f_1124_);
lean_inc(v_currMacroScope_1123_);
lean_inc(v_quotContext_1122_);
lean_inc(v_maxHeartbeats_1121_);
lean_inc(v_initHeartbeats_1120_);
lean_inc(v_openDecls_1119_);
lean_inc(v_currNamespace_1118_);
lean_inc_ref(v_fileMap_1116_);
lean_inc_ref(v_fileName_1115_);
v___y_1012_ = v___y_1153_;
v___y_1013_ = v___y_1154_;
v_fileName_1014_ = v_fileName_1115_;
v_fileMap_1015_ = v_fileMap_1116_;
v_currNamespace_1016_ = v_currNamespace_1118_;
v_openDecls_1017_ = v_openDecls_1119_;
v_initHeartbeats_1018_ = v_initHeartbeats_1120_;
v_maxHeartbeats_1019_ = v_maxHeartbeats_1121_;
v_quotContext_1020_ = v_quotContext_1122_;
v_currMacroScope_1021_ = v_currMacroScope_1123_;
v_cancelTk_x3f_1022_ = v_cancelTk_x3f_1124_;
v_inheritedTraceOptions_1023_ = v_inheritedTraceOptions_1125_;
v_currRecDepth_1024_ = v_currRecDepth_1111_;
v_ref_1025_ = v_ref_1112_;
v_suppressElabErrors_1026_ = v_suppressElabErrors_1113_;
v_isRecordingDeps_1027_ = v_isRecordingDeps_1114_;
v___y_1028_ = v___y_988_;
goto v___jp_1011_;
}
}
v___jp_1156_:
{
if (v___y_1160_ == 0)
{
if (v___y_1158_ == 0)
{
v___y_1152_ = v___y_1160_;
v___y_1153_ = v___y_1157_;
v___y_1154_ = v___y_1159_;
v___y_1155_ = v_a_983_;
goto v___jp_1151_;
}
else
{
v___y_1127_ = v___y_1160_;
v___y_1128_ = v___y_1157_;
v___y_1129_ = v___y_1159_;
goto v___jp_1126_;
}
}
else
{
v___y_1152_ = v___y_1160_;
v___y_1153_ = v___y_1157_;
v___y_1154_ = v___y_1159_;
v___y_1155_ = v___y_1158_;
goto v___jp_1151_;
}
}
v___jp_1161_:
{
uint16_t v___x_1163_; lean_object* v___x_1164_; lean_object* v_env_1165_; uint8_t v___x_1166_; uint16_t v___x_1167_; uint16_t v___x_1168_; uint16_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1163_ = l_Lean_OptionFlags_ofOptions(v___y_1162_);
v___x_1164_ = lean_st_ref_get(v___y_988_);
v_env_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_env_1165_);
lean_dec(v___x_1164_);
v___x_1166_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1165_);
lean_dec_ref(v_env_1165_);
v___x_1167_ = 512;
v___x_1168_ = lean_uint16_land(v___x_1163_, v___x_1167_);
v___x_1169_ = 0;
v___x_1170_ = lean_uint16_dec_eq(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
v___y_1157_ = v___x_1163_;
v___y_1158_ = v___x_1166_;
v___y_1159_ = v___y_1162_;
v___y_1160_ = v_a_983_;
goto v___jp_1156_;
}
else
{
v___y_1157_ = v___x_1163_;
v___y_1158_ = v___x_1166_;
v___y_1159_ = v___y_1162_;
v___y_1160_ = v_val_984_;
goto v___jp_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed(lean_object* v_kind_1174_, lean_object* v_a_1175_, lean_object* v___x_1176_, lean_object* v_diag_1177_, lean_object* v___x_1178_, lean_object* v_a_1179_, lean_object* v_val_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v___x_26982__boxed_1186_; uint8_t v_a_26984__boxed_1187_; uint8_t v_val_26985__boxed_1188_; lean_object* v_res_1189_; 
v___x_26982__boxed_1186_ = lean_unbox(v___x_1176_);
v_a_26984__boxed_1187_ = lean_unbox(v_a_1179_);
v_val_26985__boxed_1188_ = lean_unbox(v_val_1180_);
v_res_1189_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(v_kind_1174_, v_a_1175_, v___x_26982__boxed_1186_, v_diag_1177_, v___x_1178_, v_a_26984__boxed_1187_, v_val_26985__boxed_1188_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___x_1178_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object* v_kind_1195_, uint8_t v_a_1196_, uint8_t v_val_1197_, lean_object* v_as_x27_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
if (lean_obj_tag(v_as_x27_1198_) == 0)
{
lean_object* v___x_1205_; 
lean_dec_ref(v_kind_1195_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_b_1199_);
return v___x_1205_;
}
else
{
lean_object* v_head_1206_; lean_object* v_tail_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_mctx_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_b_1199_);
v_head_1206_ = lean_ctor_get(v_as_x27_1198_, 0);
v_tail_1207_ = lean_ctor_get(v_as_x27_1198_, 1);
v___x_1208_ = lean_box(0);
v___x_1209_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0));
v___x_1210_ = lean_st_ref_get(v___y_1201_);
v_mctx_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_ref(v_mctx_1211_);
lean_dec(v___x_1210_);
v___x_1212_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1211_, v_head_1206_);
lean_dec_ref(v_mctx_1211_);
if (lean_obj_tag(v___x_1212_) == 1)
{
lean_object* v_val_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1266_; 
v_val_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1266_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_val_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1266_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_lctx_1217_; lean_object* v_type_1218_; lean_object* v___x_1219_; lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v_diag_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v_lctx_1217_ = lean_ctor_get(v_val_1213_, 1);
lean_inc_ref(v_lctx_1217_);
v_type_1218_ = lean_ctor_get(v_val_1213_, 2);
lean_inc_ref(v_type_1218_);
lean_dec(v_val_1213_);
v___x_1219_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_1218_, v___y_1201_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = lean_st_ref_get(v___y_1201_);
v_diag_1222_ = lean_ctor_get(v___x_1221_, 4);
lean_inc_ref_n(v_diag_1222_, 2);
lean_dec(v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__1));
v___x_1225_ = 1;
v___x_1226_ = lean_box(v___x_1225_);
v___x_1227_ = lean_box(v_a_1196_);
v___x_1228_ = lean_box(v_val_1197_);
lean_inc_ref(v_kind_1195_);
v___f_1229_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1229_, 0, v_kind_1195_);
lean_closure_set(v___f_1229_, 1, v_a_1220_);
lean_closure_set(v___f_1229_, 2, v___x_1226_);
lean_closure_set(v___f_1229_, 3, v_diag_1222_);
lean_closure_set(v___f_1229_, 4, v___x_1223_);
lean_closure_set(v___f_1229_, 5, v___x_1227_);
lean_closure_set(v___f_1229_, 6, v___x_1228_);
v___x_1230_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(v_lctx_1217_, v___x_1224_, v___f_1229_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1257_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1257_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1257_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v_mctx_1236_; lean_object* v_cache_1237_; lean_object* v_zetaDeltaFVarIds_1238_; lean_object* v_postponed_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1255_; 
v___x_1235_ = lean_st_ref_take(v___y_1201_);
v_mctx_1236_ = lean_ctor_get(v___x_1235_, 0);
v_cache_1237_ = lean_ctor_get(v___x_1235_, 1);
v_zetaDeltaFVarIds_1238_ = lean_ctor_get(v___x_1235_, 2);
v_postponed_1239_ = lean_ctor_get(v___x_1235_, 3);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1235_, 4);
lean_dec(v_unused_1256_);
v___x_1241_ = v___x_1235_;
v_isShared_1242_ = v_isSharedCheck_1255_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_postponed_1239_);
lean_inc(v_zetaDeltaFVarIds_1238_);
lean_inc(v_cache_1237_);
lean_inc(v_mctx_1236_);
lean_dec(v___x_1235_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1255_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 4, v_diag_1222_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_mctx_1236_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_cache_1237_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1238_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1239_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1222_);
v___x_1244_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_st_ref_put(v___y_1201_, v___x_1244_);
if (lean_obj_tag(v_a_1231_) == 1)
{
lean_object* v___x_1247_; 
lean_dec_ref(v_kind_1195_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v_a_1231_);
v___x_1247_ = v___x_1215_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1231_);
v___x_1247_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___x_1208_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1248_);
v___x_1250_ = v___x_1233_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_del_object(v___x_1233_);
lean_dec(v_a_1231_);
lean_del_object(v___x_1215_);
v_as_x27_1198_ = v_tail_1207_;
v_b_1199_ = v___x_1209_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v_diag_1222_);
lean_del_object(v___x_1215_);
lean_dec_ref(v_kind_1195_);
v_a_1258_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1230_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1230_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_dec(v___x_1212_);
v_as_x27_1198_ = v_tail_1207_;
v_b_1199_ = v___x_1209_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object* v_kind_1268_, lean_object* v_a_1269_, lean_object* v_val_1270_, lean_object* v_as_x27_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v_a_27319__boxed_1278_; uint8_t v_val_27320__boxed_1279_; lean_object* v_res_1280_; 
v_a_27319__boxed_1278_ = lean_unbox(v_a_1269_);
v_val_27320__boxed_1279_ = lean_unbox(v_val_1270_);
v_res_1280_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1268_, v_a_27319__boxed_1278_, v_val_27320__boxed_1279_, v_as_x27_1271_, v_b_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v_as_x27_1271_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(uint8_t v_a_1281_, uint8_t v_val_1282_, lean_object* v_kind_1283_, lean_object* v_goals_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0));
v___x_1292_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1283_, v_a_1281_, v_val_1282_, v_goals_1284_, v___x_1291_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1305_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1305_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1305_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_fst_1297_; 
v_fst_1297_ = lean_ctor_get(v_a_1293_, 0);
lean_inc(v_fst_1297_);
lean_dec(v_a_1293_);
if (lean_obj_tag(v_fst_1297_) == 0)
{
lean_object* v___x_1299_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1290_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1290_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
else
{
lean_object* v_val_1301_; lean_object* v___x_1303_; 
v_val_1301_ = lean_ctor_get(v_fst_1297_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v_fst_1297_, 1);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_val_1301_);
v___x_1303_ = v___x_1295_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_val_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_a_1306_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1292_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1292_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed(lean_object* v_a_1314_, lean_object* v_val_1315_, lean_object* v_kind_1316_, lean_object* v_goals_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v_a_27460__boxed_1323_; uint8_t v_val_27461__boxed_1324_; lean_object* v_res_1325_; 
v_a_27460__boxed_1323_ = lean_unbox(v_a_1314_);
v_val_27461__boxed_1324_ = lean_unbox(v_val_1315_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(v_a_27460__boxed_1323_, v_val_27461__boxed_1324_, v_kind_1316_, v_goals_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v_goals_1317_);
return v_res_1325_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = lean_box(1);
v___x_1329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_1330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0);
v___x_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
lean_ctor_set(v___x_1331_, 2, v___x_1328_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(lean_object* v_val_1333_, uint8_t v_a_1334_, lean_object* v___x_1335_, lean_object* v_ci_1336_, lean_object* v_info_1337_, lean_object* v_x_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_a_1343_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = lean_st_ref_get(v_val_1333_);
v___x_1351_ = lean_unbox(v___x_1350_);
if (v___x_1351_ == 0)
{
if (lean_obj_tag(v_info_1337_) == 0)
{
lean_object* v_toCommandContextInfo_1352_; lean_object* v_i_1353_; lean_object* v_parentDecl_x3f_1354_; lean_object* v_autoImplicits_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1413_; 
v_toCommandContextInfo_1352_ = lean_ctor_get(v_ci_1336_, 0);
lean_inc_ref(v_toCommandContextInfo_1352_);
v_i_1353_ = lean_ctor_get(v_info_1337_, 0);
lean_inc_ref(v_i_1353_);
lean_dec_ref_known(v_info_1337_, 1);
v_parentDecl_x3f_1354_ = lean_ctor_get(v_ci_1336_, 1);
v_autoImplicits_1355_ = lean_ctor_get(v_ci_1336_, 2);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_ci_1336_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_ci_1336_, 0);
lean_dec(v_unused_1414_);
v___x_1357_ = v_ci_1336_;
v_isShared_1358_ = v_isSharedCheck_1413_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_autoImplicits_1355_);
lean_inc(v_parentDecl_x3f_1354_);
lean_dec(v_ci_1336_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1413_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_env_1359_; lean_object* v_cmdEnv_x3f_1360_; lean_object* v_fileMap_1361_; lean_object* v_options_1362_; lean_object* v_currNamespace_1363_; lean_object* v_openDecls_1364_; lean_object* v_ngen_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1411_; 
v_env_1359_ = lean_ctor_get(v_toCommandContextInfo_1352_, 0);
v_cmdEnv_x3f_1360_ = lean_ctor_get(v_toCommandContextInfo_1352_, 1);
v_fileMap_1361_ = lean_ctor_get(v_toCommandContextInfo_1352_, 2);
v_options_1362_ = lean_ctor_get(v_toCommandContextInfo_1352_, 4);
v_currNamespace_1363_ = lean_ctor_get(v_toCommandContextInfo_1352_, 5);
v_openDecls_1364_ = lean_ctor_get(v_toCommandContextInfo_1352_, 6);
v_ngen_1365_ = lean_ctor_get(v_toCommandContextInfo_1352_, 7);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_toCommandContextInfo_1352_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_toCommandContextInfo_1352_, 3);
lean_dec(v_unused_1412_);
v___x_1367_ = v_toCommandContextInfo_1352_;
v_isShared_1368_ = v_isSharedCheck_1411_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_ngen_1365_);
lean_inc(v_openDecls_1364_);
lean_inc(v_currNamespace_1363_);
lean_inc(v_options_1362_);
lean_inc(v_fileMap_1361_);
lean_inc(v_cmdEnv_x3f_1360_);
lean_inc(v_env_1359_);
lean_dec(v_toCommandContextInfo_1352_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1411_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_toElabInfo_1369_; lean_object* v_mctxBefore_1370_; lean_object* v_goalsBefore_1371_; lean_object* v_mctxAfter_1372_; lean_object* v_goalsAfter_1373_; lean_object* v_val_1375_; lean_object* v___x_1381_; 
v_toElabInfo_1369_ = lean_ctor_get(v_i_1353_, 0);
lean_inc_ref(v_toElabInfo_1369_);
v_mctxBefore_1370_ = lean_ctor_get(v_i_1353_, 1);
lean_inc_ref(v_mctxBefore_1370_);
v_goalsBefore_1371_ = lean_ctor_get(v_i_1353_, 2);
lean_inc(v_goalsBefore_1371_);
v_mctxAfter_1372_ = lean_ctor_get(v_i_1353_, 3);
lean_inc_ref(v_mctxAfter_1372_);
v_goalsAfter_1373_ = lean_ctor_get(v_i_1353_, 4);
lean_inc(v_goalsAfter_1373_);
lean_dec_ref(v_i_1353_);
lean_inc_ref(v_ngen_1365_);
lean_inc(v_openDecls_1364_);
lean_inc(v_currNamespace_1363_);
lean_inc_ref(v_options_1362_);
lean_inc_ref(v_fileMap_1361_);
lean_inc(v_cmdEnv_x3f_1360_);
lean_inc_ref(v_env_1359_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 3, v_mctxBefore_1370_);
v___x_1381_ = v___x_1367_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_env_1359_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_cmdEnv_x3f_1360_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_fileMap_1361_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_mctxBefore_1370_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_options_1362_);
lean_ctor_set(v_reuseFailAlloc_1410_, 5, v_currNamespace_1363_);
lean_ctor_set(v_reuseFailAlloc_1410_, 6, v_openDecls_1364_);
lean_ctor_set(v_reuseFailAlloc_1410_, 7, v_ngen_1365_);
v___x_1381_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1380_;
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_stx_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_box(v_a_1334_);
v___x_1377_ = lean_st_ref_swap(v_val_1333_, v___x_1376_);
lean_dec(v___x_1377_);
v_stx_1378_ = lean_ctor_get(v_toElabInfo_1369_, 1);
lean_inc(v_stx_1378_);
lean_dec_ref(v_toElabInfo_1369_);
v___x_1379_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v___x_1335_, v_stx_1378_, v_val_1375_, v___y_1339_, v___y_1340_);
return v___x_1379_;
}
v_reusejp_1380_:
{
lean_object* v___x_1383_; 
lean_inc_ref(v_autoImplicits_1355_);
lean_inc(v_parentDecl_x3f_1354_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1381_);
v___x_1383_ = v___x_1357_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_parentDecl_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_autoImplicits_1355_);
v___x_1383_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1384_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1384_, 0, v_env_1359_);
lean_ctor_set(v___x_1384_, 1, v_cmdEnv_x3f_1360_);
lean_ctor_set(v___x_1384_, 2, v_fileMap_1361_);
lean_ctor_set(v___x_1384_, 3, v_mctxAfter_1372_);
lean_ctor_set(v___x_1384_, 4, v_options_1362_);
lean_ctor_set(v___x_1384_, 5, v_currNamespace_1363_);
lean_ctor_set(v___x_1384_, 6, v_openDecls_1364_);
lean_ctor_set(v___x_1384_, 7, v_ngen_1365_);
v___x_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v_parentDecl_x3f_1354_);
lean_ctor_set(v___x_1385_, 2, v_autoImplicits_1355_);
v___x_1386_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1);
v___x_1387_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7));
v___x_1388_ = lean_box(v_a_1334_);
lean_inc(v___x_1350_);
v___x_1389_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed), 9, 4);
lean_closure_set(v___x_1389_, 0, v___x_1388_);
lean_closure_set(v___x_1389_, 1, v___x_1350_);
lean_closure_set(v___x_1389_, 2, v___x_1387_);
lean_closure_set(v___x_1389_, 3, v_goalsBefore_1371_);
v___x_1390_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_1383_, v___x_1386_, v___x_1389_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
if (lean_obj_tag(v_a_1391_) == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__2));
v___x_1393_ = lean_box(v_a_1334_);
v___x_1394_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed), 9, 4);
lean_closure_set(v___x_1394_, 0, v___x_1393_);
lean_closure_set(v___x_1394_, 1, v___x_1350_);
lean_closure_set(v___x_1394_, 2, v___x_1392_);
lean_closure_set(v___x_1394_, 3, v_goalsAfter_1373_);
v___x_1395_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_1385_, v___x_1386_, v___x_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1405_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_a_1396_) == 1)
{
lean_object* v_val_1400_; 
lean_del_object(v___x_1398_);
v_val_1400_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v_a_1396_, 1);
v_val_1375_ = v_val_1400_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_dec(v_a_1396_);
lean_dec_ref(v_toElabInfo_1369_);
lean_dec_ref(v___x_1335_);
v___x_1401_ = lean_box(0);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1401_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1406_; 
lean_dec_ref(v_toElabInfo_1369_);
lean_dec_ref(v___x_1335_);
v_a_1406_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1395_, 1);
v_a_1343_ = v_a_1406_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_val_1407_; 
lean_dec_ref_known(v___x_1385_, 3);
lean_dec(v_goalsAfter_1373_);
lean_dec(v___x_1350_);
v_val_1407_ = lean_ctor_get(v_a_1391_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v_a_1391_, 1);
v_val_1375_ = v_val_1407_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1408_; 
lean_dec_ref_known(v___x_1385_, 3);
lean_dec(v_goalsAfter_1373_);
lean_dec_ref(v_toElabInfo_1369_);
lean_dec(v___x_1350_);
lean_dec_ref(v___x_1335_);
v_a_1408_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1390_, 1);
v_a_1343_ = v_a_1408_;
goto v___jp_1342_;
}
}
}
}
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec(v___x_1350_);
lean_dec_ref(v_info_1337_);
lean_dec_ref(v_ci_1336_);
lean_dec_ref(v___x_1335_);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec(v___x_1350_);
lean_dec_ref(v_info_1337_);
lean_dec_ref(v_ci_1336_);
lean_dec_ref(v___x_1335_);
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
v___jp_1342_:
{
lean_object* v_ref_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_ref_1344_ = lean_ctor_get(v___y_1339_, 7);
v___x_1345_ = lean_io_error_to_string(v_a_1343_);
v___x_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = l_Lean_MessageData_ofFormat(v___x_1346_);
lean_inc(v_ref_1344_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_ref_1344_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed(lean_object* v_val_1419_, lean_object* v_a_1420_, lean_object* v___x_1421_, lean_object* v_ci_1422_, lean_object* v_info_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
uint8_t v_a_27555__boxed_1428_; lean_object* v_res_1429_; 
v_a_27555__boxed_1428_ = lean_unbox(v_a_1420_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(v_val_1419_, v_a_27555__boxed_1428_, v___x_1421_, v_ci_1422_, v_info_1423_, v_x_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_x_1424_);
lean_dec(v_val_1419_);
return v_res_1429_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_instMonadEIO___redArg();
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(lean_object* v_msg_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_toApplicative_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1470_; 
v___x_1437_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0);
v___x_1438_ = l_StateRefT_x27_instMonad___redArg(v___x_1437_);
v_toApplicative_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1438_, 1);
lean_dec(v_unused_1471_);
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1470_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_toApplicative_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1470_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_toFunctor_1443_; lean_object* v_toSeq_1444_; lean_object* v_toSeqLeft_1445_; lean_object* v_toSeqRight_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1468_; 
v_toFunctor_1443_ = lean_ctor_get(v_toApplicative_1439_, 0);
v_toSeq_1444_ = lean_ctor_get(v_toApplicative_1439_, 2);
v_toSeqLeft_1445_ = lean_ctor_get(v_toApplicative_1439_, 3);
v_toSeqRight_1446_ = lean_ctor_get(v_toApplicative_1439_, 4);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_toApplicative_1439_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_toApplicative_1439_, 1);
lean_dec(v_unused_1469_);
v___x_1448_ = v_toApplicative_1439_;
v_isShared_1449_ = v_isSharedCheck_1468_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_toSeqRight_1446_);
lean_inc(v_toSeqLeft_1445_);
lean_inc(v_toSeq_1444_);
lean_inc(v_toFunctor_1443_);
lean_dec(v_toApplicative_1439_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1468_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___f_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___x_1459_; 
v___f_1450_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__1));
v___f_1451_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__2));
lean_inc_ref(v_toFunctor_1443_);
v___f_1452_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1452_, 0, v_toFunctor_1443_);
v___f_1453_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1453_, 0, v_toFunctor_1443_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___f_1452_);
lean_ctor_set(v___x_1454_, 1, v___f_1453_);
v___f_1455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1455_, 0, v_toSeqRight_1446_);
v___f_1456_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1456_, 0, v_toSeqLeft_1445_);
v___f_1457_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1457_, 0, v_toSeq_1444_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 4, v___f_1455_);
lean_ctor_set(v___x_1448_, 3, v___f_1456_);
lean_ctor_set(v___x_1448_, 2, v___f_1457_);
lean_ctor_set(v___x_1448_, 1, v___f_1450_);
lean_ctor_set(v___x_1448_, 0, v___x_1454_);
v___x_1459_ = v___x_1448_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___f_1450_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v___f_1457_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___f_1456_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v___f_1455_);
v___x_1459_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v___f_1451_);
lean_ctor_set(v___x_1441_, 0, v___x_1459_);
v___x_1461_ = v___x_1441_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___f_1451_);
v___x_1461_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_22806__overap_1464_; lean_object* v___x_1465_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_instInhabitedOfMonad___redArg(v___x_1461_, v___x_1462_);
v___x_22806__overap_1464_ = lean_panic_fn_borrowed(v___x_1463_, v_msg_1433_);
lean_dec(v___x_1463_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
v___x_1465_ = lean_apply_3(v___x_22806__overap_1464_, v___y_1434_, v___y_1435_, lean_box(0));
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v_msg_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1476_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__2));
v___x_1481_ = lean_unsigned_to_nat(21u);
v___x_1482_ = lean_unsigned_to_nat(65u);
v___x_1483_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__1));
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__0));
v___x_1485_ = l_mkPanicMessageWithDecl(v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_, v___x_1480_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(lean_object* v_preNode_1486_, lean_object* v_postNode_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
switch(lean_obj_tag(v_x_1489_))
{
case 0:
{
lean_object* v_i_1493_; lean_object* v_t_1494_; lean_object* v___x_1495_; 
v_i_1493_ = lean_ctor_get(v_x_1489_, 0);
lean_inc_ref(v_i_1493_);
v_t_1494_ = lean_ctor_get(v_x_1489_, 1);
lean_inc_ref(v_t_1494_);
lean_dec_ref_known(v_x_1489_, 2);
v___x_1495_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1493_, v_x_1488_);
v_x_1488_ = v___x_1495_;
v_x_1489_ = v_t_1494_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1488_) == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref_known(v_x_1489_, 2);
lean_dec_ref(v_postNode_1487_);
lean_dec_ref(v_preNode_1486_);
v___x_1497_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3);
v___x_1498_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v___x_1497_, v___y_1490_, v___y_1491_);
return v___x_1498_;
}
else
{
lean_object* v_i_1499_; lean_object* v_children_1500_; lean_object* v_val_1501_; lean_object* v___x_1502_; 
v_i_1499_ = lean_ctor_get(v_x_1489_, 0);
lean_inc_ref_n(v_i_1499_, 2);
v_children_1500_ = lean_ctor_get(v_x_1489_, 1);
lean_inc_ref_n(v_children_1500_, 2);
lean_dec_ref_known(v_x_1489_, 2);
v_val_1501_ = lean_ctor_get(v_x_1488_, 0);
lean_inc_n(v_val_1501_, 2);
lean_inc_ref(v_preNode_1486_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
v___x_1502_ = lean_apply_6(v_preNode_1486_, v_val_1501_, v_i_1499_, v_children_1500_, v___y_1490_, v___y_1491_, lean_box(0));
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; uint8_t v___x_1504_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1504_ = lean_unbox(v_a_1503_);
lean_dec(v_a_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_preNode_1486_);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_x_1488_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_x_1488_, 0);
lean_dec(v_unused_1530_);
v___x_1506_ = v_x_1488_;
v_isShared_1507_ = v_isSharedCheck_1529_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_x_1488_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1529_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_box(0);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
v___x_1509_ = lean_apply_7(v_postNode_1487_, v_val_1501_, v_i_1499_, v_children_1500_, v___x_1508_, v___y_1490_, v___y_1491_, lean_box(0));
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1520_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1520_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1520_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v_a_1510_);
v___x_1515_ = v___x_1506_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1515_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_del_object(v___x_1506_);
v_a_1521_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1509_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1509_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1531_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1488_, v_i_1499_);
v___x_1532_ = l_Lean_PersistentArray_toList___redArg(v_children_1500_);
v___x_1533_ = lean_box(0);
lean_inc_ref(v_postNode_1487_);
v___x_1534_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1486_, v_postNode_1487_, v___x_1531_, v___x_1532_, v___x_1533_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
v___x_1536_ = lean_apply_7(v_postNode_1487_, v_val_1501_, v_i_1499_, v_children_1500_, v_a_1535_, v___y_1490_, v___y_1491_, lean_box(0));
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_a_1546_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1536_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1536_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_val_1501_);
lean_dec_ref(v_children_1500_);
lean_dec_ref(v_i_1499_);
lean_dec_ref(v_postNode_1487_);
v_a_1554_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1534_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1534_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_val_1501_);
lean_dec_ref(v_children_1500_);
lean_dec_ref_known(v_x_1488_, 1);
lean_dec_ref(v_i_1499_);
lean_dec_ref(v_postNode_1487_);
lean_dec_ref(v_preNode_1486_);
v_a_1562_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1502_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1502_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
default: 
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_x_1488_);
lean_dec_ref(v_postNode_1487_);
lean_dec_ref(v_preNode_1486_);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1489_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_x_1489_, 0);
lean_dec(v_unused_1578_);
v___x_1571_ = v_x_1489_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v_x_1489_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = lean_box(0);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(lean_object* v_preNode_1579_, lean_object* v_postNode_1580_, lean_object* v___x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
if (lean_obj_tag(v_x_1582_) == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec(v___x_1581_);
lean_dec_ref(v_postNode_1580_);
lean_dec_ref(v_preNode_1579_);
v___x_1587_ = l_List_reverse___redArg(v_x_1583_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
else
{
lean_object* v_head_1589_; lean_object* v_tail_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1608_; 
v_head_1589_ = lean_ctor_get(v_x_1582_, 0);
v_tail_1590_ = lean_ctor_get(v_x_1582_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1582_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1592_ = v_x_1582_;
v_isShared_1593_ = v_isSharedCheck_1608_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_tail_1590_);
lean_inc(v_head_1589_);
lean_dec(v_x_1582_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1608_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; 
lean_inc(v___x_1581_);
lean_inc_ref(v_postNode_1580_);
lean_inc_ref(v_preNode_1579_);
v___x_1594_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1579_, v_postNode_1580_, v___x_1581_, v_head_1589_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v_x_1583_);
lean_ctor_set(v___x_1592_, 0, v_a_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1595_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_x_1583_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
v_x_1582_ = v_tail_1590_;
v_x_1583_ = v___x_1597_;
goto _start;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1592_);
lean_dec(v_tail_1590_);
lean_dec(v_x_1583_);
lean_dec(v___x_1581_);
lean_dec_ref(v_postNode_1580_);
lean_dec_ref(v_preNode_1579_);
v_a_1600_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1594_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg___boxed(lean_object* v_preNode_1609_, lean_object* v_postNode_1610_, lean_object* v___x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1609_, v_postNode_1610_, v___x_1611_, v_x_1612_, v_x_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___boxed(lean_object* v_preNode_1618_, lean_object* v_postNode_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1618_, v_postNode_1619_, v_x_1620_, v_x_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(lean_object* v_postNode_1626_, lean_object* v_ci_1627_, lean_object* v_i_1628_, lean_object* v_cs_1629_, lean_object* v_x_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
v___x_1634_ = lean_apply_6(v_postNode_1626_, v_ci_1627_, v_i_1628_, v_cs_1629_, v___y_1631_, v___y_1632_, lean_box(0));
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed(lean_object* v_postNode_1635_, lean_object* v_ci_1636_, lean_object* v_i_1637_, lean_object* v_cs_1638_, lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(v_postNode_1635_, v_ci_1636_, v_i_1637_, v_cs_1638_, v_x_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v_x_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object* v_preNode_1644_, lean_object* v_postNode_1645_, lean_object* v_ctx_x3f_1646_, lean_object* v_t_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___f_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___f_1651_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1651_, 0, v_postNode_1645_);
v___x_1652_ = lean_box(0);
v___x_1653_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1644_, v___f_1651_, v_ctx_x3f_1646_, v_t_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v___x_1653_, 0);
lean_dec(v_unused_1661_);
v___x_1655_ = v___x_1653_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v___x_1653_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1652_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1652_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1653_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1653_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object* v_preNode_1670_, lean_object* v_postNode_1671_, lean_object* v_ctx_x3f_1672_, lean_object* v_t_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_preNode_1670_, v_postNode_1671_, v_ctx_x3f_1672_, v_t_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(uint8_t v_a_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_box(v_a_1678_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object* v_a_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_a_28117__boxed_1694_; lean_object* v_res_1695_; 
v_a_28117__boxed_1694_ = lean_unbox(v_a_1687_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_a_28117__boxed_1694_, v_x_1688_, v_x_1689_, v_x_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec_ref(v_x_1690_);
lean_dec_ref(v_x_1689_);
lean_dec_ref(v_x_1688_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(uint8_t v_a_1696_, lean_object* v_val_1697_, lean_object* v_as_1698_, size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_b_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v_val_1697_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_b_1701_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1707_ = lean_box(v_a_1696_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1708_, 0, v___x_1707_);
v___x_1709_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1710_ = lean_box(v_a_1696_);
lean_inc(v_val_1697_);
v___f_1711_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1711_, 0, v_val_1697_);
lean_closure_set(v___f_1711_, 1, v___x_1710_);
lean_closure_set(v___f_1711_, 2, v___x_1709_);
v___x_1712_ = lean_box(0);
v_a_1713_ = lean_array_uget_borrowed(v_as_1698_, v_i_1700_);
v___x_1714_ = lean_box(0);
lean_inc(v_a_1713_);
v___x_1715_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___f_1708_, v___f_1711_, v___x_1714_, v_a_1713_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1715_) == 0)
{
size_t v___x_1716_; size_t v___x_1717_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1700_, v___x_1716_);
v_i_1700_ = v___x_1717_;
v_b_1701_ = v___x_1712_;
goto _start;
}
else
{
lean_dec(v_val_1697_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object* v_a_1719_, lean_object* v_val_1720_, lean_object* v_as_1721_, lean_object* v_sz_1722_, lean_object* v_i_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v_a_28142__boxed_1728_; size_t v_sz_boxed_1729_; size_t v_i_boxed_1730_; lean_object* v_res_1731_; 
v_a_28142__boxed_1728_ = lean_unbox(v_a_1719_);
v_sz_boxed_1729_ = lean_unbox_usize(v_sz_1722_);
lean_dec(v_sz_1722_);
v_i_boxed_1730_ = lean_unbox_usize(v_i_1723_);
lean_dec(v_i_1723_);
v_res_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_a_28142__boxed_1728_, v_val_1720_, v_as_1721_, v_sz_boxed_1729_, v_i_boxed_1730_, v_b_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v_as_1721_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object* v_opt_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_scopes_1737_; lean_object* v___x_1738_; lean_object* v_opts_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1735_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1736_ = lean_st_ref_get(v___y_1733_);
v_scopes_1737_ = lean_ctor_get(v___x_1736_, 2);
lean_inc(v_scopes_1737_);
lean_dec(v___x_1736_);
v___x_1738_ = l_List_head_x21___redArg(v___x_1735_, v_scopes_1737_);
lean_dec(v_scopes_1737_);
v_opts_1739_ = lean_ctor_get(v___x_1738_, 1);
lean_inc_ref(v_opts_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_1739_, v_opt_1732_);
lean_dec_ref(v_opts_1739_);
v___x_1741_ = lean_box(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object* v_opt_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v_opt_1743_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object* v___cmdStx_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1782_; 
v___x_1751_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1752_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_1751_, v___y_1749_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1782_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1782_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_unbox(v_a_1753_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec(v_a_1753_);
v___x_1758_ = lean_box(0);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v_infoState_1763_; lean_object* v_trees_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; size_t v_sz_1770_; size_t v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; 
lean_del_object(v___x_1755_);
v___x_1762_ = lean_st_ref_get(v___y_1749_);
v_infoState_1763_ = lean_ctor_get(v___x_1762_, 8);
lean_inc_ref(v_infoState_1763_);
lean_dec(v___x_1762_);
v_trees_1764_ = lean_ctor_get(v_infoState_1763_, 2);
lean_inc_ref(v_trees_1764_);
lean_dec_ref(v_infoState_1763_);
v___x_1765_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1764_);
lean_dec_ref(v_trees_1764_);
v___x_1766_ = 0;
v___x_1767_ = lean_box(v___x_1766_);
v___x_1768_ = lean_st_mk_ref(v___x_1767_);
v___x_1769_ = lean_box(0);
v_sz_1770_ = lean_array_size(v___x_1765_);
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = lean_unbox(v_a_1753_);
lean_dec(v_a_1753_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___x_1772_, v___x_1768_, v___x_1765_, v_sz_1770_, v___x_1771_, v___x_1769_, v___y_1748_, v___y_1749_);
lean_dec_ref(v___x_1765_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v___x_1773_, 0);
lean_dec(v_unused_1781_);
v___x_1775_ = v___x_1773_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v___x_1773_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1769_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1769_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
else
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object* v___cmdStx_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(v___cmdStx_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___cmdStx_1783_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object* v_opt_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1796_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object* v_opt_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_opt_1801_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object* v_00_u03b2_1806_, lean_object* v_m_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v_m_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object* v_00_u03b2_1809_, lean_object* v_m_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_00_u03b2_1809_, v_m_1810_);
lean_dec_ref(v_m_1810_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object* v_kind_1812_, uint8_t v_a_1813_, uint8_t v_val_1814_, lean_object* v_as_1815_, lean_object* v_as_x27_1816_, lean_object* v_b_1817_, lean_object* v_a_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1812_, v_a_1813_, v_val_1814_, v_as_x27_1816_, v_b_1817_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object* v_kind_1825_, lean_object* v_a_1826_, lean_object* v_val_1827_, lean_object* v_as_1828_, lean_object* v_as_x27_1829_, lean_object* v_b_1830_, lean_object* v_a_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
uint8_t v_a_28335__boxed_1837_; uint8_t v_val_28336__boxed_1838_; lean_object* v_res_1839_; 
v_a_28335__boxed_1837_ = lean_unbox(v_a_1826_);
v_val_28336__boxed_1838_ = lean_unbox(v_val_1827_);
v_res_1839_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_kind_1825_, v_a_28335__boxed_1837_, v_val_28336__boxed_1838_, v_as_1828_, v_as_x27_1829_, v_b_1830_, v_a_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v_as_x27_1829_);
lean_dec(v_as_1828_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_x_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(v_00_u03b2_1844_, v_x_1845_, v_x_1846_);
lean_dec(v_x_1846_);
lean_dec_ref(v_x_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_x_1849_, v_x_1850_, v_x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(lean_object* v_00_u03c3_1853_, lean_object* v_00_u03b2_1854_, lean_object* v_map_1855_, lean_object* v_init_1856_, lean_object* v_f_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_map_1855_, v_init_1856_, v_f_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_map_1861_, lean_object* v_init_1862_, lean_object* v_f_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(v_00_u03c3_1859_, v_00_u03b2_1860_, v_map_1861_, v_init_1862_, v_f_1863_);
lean_dec_ref(v_map_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(lean_object* v_00_u03c3_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_map_1867_, lean_object* v_f_1868_, lean_object* v_init_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_map_1867_, v_f_1868_, v_init_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___boxed(lean_object* v_00_u03c3_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_map_1873_, lean_object* v_f_1874_, lean_object* v_init_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(v_00_u03c3_1871_, v_00_u03b2_1872_, v_map_1873_, v_f_1874_, v_init_1875_);
lean_dec_ref(v_map_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(lean_object* v_00_u03b1_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v_msg_1878_, v___y_1879_, v___y_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b1_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(v_00_u03b1_1883_, v_msg_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(lean_object* v_00_u03b1_1889_, lean_object* v_preNode_1890_, lean_object* v_postNode_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1890_, v_postNode_1891_, v_x_1892_, v_x_1893_, v___y_1894_, v___y_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_preNode_1899_, lean_object* v_postNode_1900_, lean_object* v_x_1901_, lean_object* v_x_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(v_00_u03b1_1898_, v_preNode_1899_, v_postNode_1900_, v_x_1901_, v_x_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1907_, lean_object* v_x_1908_, size_t v_x_1909_, lean_object* v_x_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_1908_, v_x_1909_, v_x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_){
_start:
{
size_t v_x_28410__boxed_1916_; lean_object* v_res_1917_; 
v_x_28410__boxed_1916_ = lean_unbox_usize(v_x_1914_);
lean_dec(v_x_1914_);
v_res_1917_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(v_00_u03b2_1912_, v_x_1913_, v_x_28410__boxed_1916_, v_x_1915_);
lean_dec(v_x_1915_);
lean_dec_ref(v_x_1913_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1918_, lean_object* v_x_1919_, size_t v_x_1920_, size_t v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_1919_, v_x_1920_, v_x_1921_, v_x_1922_, v_x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
size_t v_x_28421__boxed_1931_; size_t v_x_28422__boxed_1932_; lean_object* v_res_1933_; 
v_x_28421__boxed_1931_ = lean_unbox_usize(v_x_1927_);
lean_dec(v_x_1927_);
v_x_28422__boxed_1932_ = lean_unbox_usize(v_x_1928_);
lean_dec(v_x_1928_);
v_res_1933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(v_00_u03b2_1925_, v_x_1926_, v_x_28421__boxed_1931_, v_x_28422__boxed_1932_, v_x_1929_, v_x_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10___redArg(lean_object* v_map_1934_, lean_object* v_f_1935_, lean_object* v_init_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_1935_, v_map_1934_, v_init_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10(lean_object* v_00_u03c3_1938_, lean_object* v_00_u03c3_1939_, lean_object* v_00_u03b2_1940_, lean_object* v_map_1941_, lean_object* v_f_1942_, lean_object* v_init_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_1942_, v_map_1941_, v_init_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(lean_object* v_map_1945_, lean_object* v_f_1946_, lean_object* v_init_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_1946_, v_map_1945_, v_init_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_map_1949_, lean_object* v_f_1950_, lean_object* v_init_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(v_map_1949_, v_f_1950_, v_init_1951_);
lean_dec_ref(v_map_1949_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(lean_object* v_00_u03c3_1953_, lean_object* v_00_u03b2_1954_, lean_object* v_map_1955_, lean_object* v_f_1956_, lean_object* v_init_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_1956_, v_map_1955_, v_init_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03c3_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_map_1961_, lean_object* v_f_1962_, lean_object* v_init_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(v_00_u03c3_1959_, v_00_u03b2_1960_, v_map_1961_, v_f_1962_, v_init_1963_);
lean_dec_ref(v_map_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(lean_object* v_msgData_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v_msgData_1965_, v___y_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___boxed(lean_object* v_msgData_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(v_msgData_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(lean_object* v_00_u03b1_1975_, lean_object* v_preNode_1976_, lean_object* v_postNode_1977_, lean_object* v___x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1976_, v_postNode_1977_, v___x_1978_, v_x_1979_, v_x_1980_, v___y_1981_, v___y_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___boxed(lean_object* v_00_u03b1_1985_, lean_object* v_preNode_1986_, lean_object* v_postNode_1987_, lean_object* v___x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(v_00_u03b1_1985_, v_preNode_1986_, v_postNode_1987_, v___x_1988_, v_x_1989_, v_x_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1995_, lean_object* v_keys_1996_, lean_object* v_vals_1997_, lean_object* v_heq_1998_, lean_object* v_i_1999_, lean_object* v_k_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1996_, v_vals_1997_, v_i_1999_, v_k_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_2002_, lean_object* v_keys_2003_, lean_object* v_vals_2004_, lean_object* v_heq_2005_, lean_object* v_i_2006_, lean_object* v_k_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_2002_, v_keys_2003_, v_vals_2004_, v_heq_2005_, v_i_2006_, v_k_2007_);
lean_dec(v_k_2007_);
lean_dec_ref(v_vals_2004_);
lean_dec_ref(v_keys_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18(lean_object* v_00_u03b2_2009_, lean_object* v_n_2010_, lean_object* v_k_2011_, lean_object* v_v_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(v_n_2010_, v_k_2011_, v_v_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(lean_object* v_00_u03b2_2014_, size_t v_depth_2015_, lean_object* v_keys_2016_, lean_object* v_vals_2017_, lean_object* v_heq_2018_, lean_object* v_i_2019_, lean_object* v_entries_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_depth_2015_, v_keys_2016_, v_vals_2017_, v_i_2019_, v_entries_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___boxed(lean_object* v_00_u03b2_2022_, lean_object* v_depth_2023_, lean_object* v_keys_2024_, lean_object* v_vals_2025_, lean_object* v_heq_2026_, lean_object* v_i_2027_, lean_object* v_entries_2028_){
_start:
{
size_t v_depth_boxed_2029_; lean_object* v_res_2030_; 
v_depth_boxed_2029_ = lean_unbox_usize(v_depth_2023_);
lean_dec(v_depth_2023_);
v_res_2030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(v_00_u03b2_2022_, v_depth_boxed_2029_, v_keys_2024_, v_vals_2025_, v_heq_2026_, v_i_2027_, v_entries_2028_);
lean_dec_ref(v_vals_2025_);
lean_dec_ref(v_keys_2024_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22(lean_object* v_00_u03c3_2031_, lean_object* v_00_u03c3_2032_, lean_object* v_00_u03b1_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_f_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_2035_, v_x_2036_, v_x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(lean_object* v_00_u03c3_2039_, lean_object* v_00_u03b1_2040_, lean_object* v_00_u03b2_2041_, lean_object* v_f_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_2042_, v_x_2043_, v_x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___boxed(lean_object* v_00_u03c3_2046_, lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_f_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(v_00_u03c3_2046_, v_00_u03b1_2047_, v_00_u03b2_2048_, v_f_2049_, v_x_2050_, v_x_2051_);
lean_dec_ref(v_x_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24(lean_object* v_00_u03b2_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(v_x_2054_, v_x_2055_, v_x_2056_, v_x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_00_u03c3_2061_, lean_object* v_00_u03c3_2062_, lean_object* v_f_2063_, lean_object* v_as_2064_, size_t v_i_2065_, size_t v_stop_2066_, lean_object* v_b_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_2063_, v_as_2064_, v_i_2065_, v_stop_2066_, v_b_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_00_u03c3_2071_, lean_object* v_00_u03c3_2072_, lean_object* v_f_2073_, lean_object* v_as_2074_, lean_object* v_i_2075_, lean_object* v_stop_2076_, lean_object* v_b_2077_){
_start:
{
size_t v_i_boxed_2078_; size_t v_stop_boxed_2079_; lean_object* v_res_2080_; 
v_i_boxed_2078_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_stop_boxed_2079_ = lean_unbox_usize(v_stop_2076_);
lean_dec(v_stop_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(v_00_u03b1_2069_, v_00_u03b2_2070_, v_00_u03c3_2071_, v_00_u03c3_2072_, v_f_2073_, v_as_2074_, v_i_boxed_2078_, v_stop_boxed_2079_, v_b_2077_);
lean_dec_ref(v_as_2074_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(lean_object* v_00_u03c3_2081_, lean_object* v_00_u03c3_2082_, lean_object* v_00_u03b1_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_f_2085_, lean_object* v_keys_2086_, lean_object* v_vals_2087_, lean_object* v_heq_2088_, lean_object* v_i_2089_, lean_object* v_acc_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_2085_, v_keys_2086_, v_vals_2087_, v_i_2089_, v_acc_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___boxed(lean_object* v_00_u03c3_2092_, lean_object* v_00_u03c3_2093_, lean_object* v_00_u03b1_2094_, lean_object* v_00_u03b2_2095_, lean_object* v_f_2096_, lean_object* v_keys_2097_, lean_object* v_vals_2098_, lean_object* v_heq_2099_, lean_object* v_i_2100_, lean_object* v_acc_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(v_00_u03c3_2092_, v_00_u03c3_2093_, v_00_u03b1_2094_, v_00_u03b2_2095_, v_f_2096_, v_keys_2097_, v_vals_2098_, v_heq_2099_, v_i_2100_, v_acc_2101_);
lean_dec_ref(v_vals_2098_);
lean_dec_ref(v_keys_2097_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(lean_object* v_00_u03b1_2103_, lean_object* v_00_u03b2_2104_, lean_object* v_00_u03c3_2105_, lean_object* v_f_2106_, lean_object* v_as_2107_, size_t v_i_2108_, size_t v_stop_2109_, lean_object* v_b_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_2106_, v_as_2107_, v_i_2108_, v_stop_2109_, v_b_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_00_u03b2_2113_, lean_object* v_00_u03c3_2114_, lean_object* v_f_2115_, lean_object* v_as_2116_, lean_object* v_i_2117_, lean_object* v_stop_2118_, lean_object* v_b_2119_){
_start:
{
size_t v_i_boxed_2120_; size_t v_stop_boxed_2121_; lean_object* v_res_2122_; 
v_i_boxed_2120_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_stop_boxed_2121_ = lean_unbox_usize(v_stop_2118_);
lean_dec(v_stop_2118_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(v_00_u03b1_2112_, v_00_u03b2_2113_, v_00_u03c3_2114_, v_f_2115_, v_as_2116_, v_i_boxed_2120_, v_stop_boxed_2121_, v_b_2119_);
lean_dec_ref(v_as_2116_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(lean_object* v_00_u03c3_2123_, lean_object* v_00_u03b1_2124_, lean_object* v_00_u03b2_2125_, lean_object* v_f_2126_, lean_object* v_keys_2127_, lean_object* v_vals_2128_, lean_object* v_heq_2129_, lean_object* v_i_2130_, lean_object* v_acc_2131_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_2126_, v_keys_2127_, v_vals_2128_, v_i_2130_, v_acc_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2133_, lean_object* v_00_u03b1_2134_, lean_object* v_00_u03b2_2135_, lean_object* v_f_2136_, lean_object* v_keys_2137_, lean_object* v_vals_2138_, lean_object* v_heq_2139_, lean_object* v_i_2140_, lean_object* v_acc_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(v_00_u03c3_2133_, v_00_u03b1_2134_, v_00_u03b2_2135_, v_f_2136_, v_keys_2137_, v_vals_2138_, v_heq_2139_, v_i_2140_, v_acc_2141_);
lean_dec_ref(v_vals_2138_);
lean_dec_ref(v_keys_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances));
v___x_2145_ = l_Lean_Elab_Command_addLinter(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
return v_res_2147_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Diagnostics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_TacticTypeCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_2385551297____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances);
lean_dec_ref(res);
res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_TacticTypeCheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_Meta_Diagnostics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_TacticTypeCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_TacticTypeCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_TacticTypeCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_TacticTypeCheck(builtin);
}
#ifdef __cplusplus
}
#endif
