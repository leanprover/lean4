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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
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
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0(uint8_t v_suppressElabErrors_206_, uint8_t v___y_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 1)
{
lean_object* v_pre_209_; 
v_pre_209_ = lean_ctor_get(v_x_208_, 0);
if (lean_obj_tag(v_pre_209_) == 0)
{
lean_object* v_str_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_str_210_ = lean_ctor_get(v_x_208_, 1);
v___x_211_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___closed__0));
v___x_212_ = lean_string_dec_eq(v_str_210_, v___x_211_);
if (v___x_212_ == 0)
{
return v___x_212_;
}
else
{
return v_suppressElabErrors_206_;
}
}
else
{
return v___y_207_;
}
}
else
{
return v___y_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_213_, lean_object* v___y_214_, lean_object* v_x_215_){
_start:
{
uint8_t v_suppressElabErrors_boxed_216_; uint8_t v___y_25887__boxed_217_; uint8_t v_res_218_; lean_object* v_r_219_; 
v_suppressElabErrors_boxed_216_ = lean_unbox(v_suppressElabErrors_213_);
v___y_25887__boxed_217_ = lean_unbox(v___y_214_);
v_res_218_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0(v_suppressElabErrors_boxed_216_, v___y_25887__boxed_217_, v_x_215_);
lean_dec(v_x_215_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
lean_ctor_set(v___x_226_, 3, v___x_225_);
lean_ctor_set(v___x_226_, 4, v___x_224_);
lean_ctor_set(v___x_226_, 5, v___x_224_);
lean_ctor_set(v___x_226_, 6, v___x_224_);
lean_ctor_set(v___x_226_, 7, v___x_224_);
lean_ctor_set(v___x_226_, 8, v___x_224_);
lean_ctor_set(v___x_226_, 9, v___x_224_);
lean_ctor_set(v___x_226_, 10, v___x_224_);
lean_ctor_set(v___x_226_, 11, v___x_223_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(32u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4(void){
_start:
{
size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_230_ = ((size_t)5ULL);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_unsigned_to_nat(32u);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_232_);
v___x_234_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3);
v___x_235_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_231_);
lean_ctor_set(v___x_235_, 3, v___x_231_);
lean_ctor_set_usize(v___x_235_, 4, v___x_230_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_box(1);
v___x_237_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_236_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(lean_object* v_msgData_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; lean_object* v_env_244_; uint8_t v___x_245_; lean_object* v_env_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_scopes_249_; lean_object* v___x_250_; lean_object* v_opts_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_243_ = lean_st_ref_get(v___y_241_);
v_env_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref(v_env_244_);
lean_dec(v___x_243_);
v___x_245_ = 0;
v_env_246_ = l_Lean_Environment_setRecordingDeps(v_env_244_, v___x_245_);
v___x_247_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_248_ = lean_st_ref_get(v___y_241_);
v_scopes_249_ = lean_ctor_get(v___x_248_, 2);
lean_inc(v_scopes_249_);
lean_dec(v___x_248_);
v___x_250_ = l_List_head_x21___redArg(v___x_247_, v_scopes_249_);
lean_dec(v_scopes_249_);
v_opts_251_ = lean_ctor_get(v___x_250_, 1);
lean_inc_ref(v_opts_251_);
lean_dec(v___x_250_);
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2);
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5);
v___x_254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_254_, 0, v_env_246_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
lean_ctor_set(v___x_254_, 3, v_opts_251_);
v___x_255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_msgData_240_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___boxed(lean_object* v_msgData_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v_msgData_257_, v___y_258_);
lean_dec(v___y_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(lean_object* v_ref_262_, lean_object* v_msgData_263_, uint8_t v_severity_264_, uint8_t v_isSilent_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; uint8_t v___y_335_; uint8_t v___y_336_; uint8_t v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; uint8_t v___y_363_; uint8_t v___y_364_; uint8_t v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; uint8_t v___y_371_; uint8_t v___y_372_; uint8_t v___y_373_; uint8_t v___x_388_; uint8_t v___y_390_; uint8_t v___y_391_; uint8_t v___y_392_; uint8_t v___y_394_; uint8_t v___x_406_; 
v___x_388_ = 2;
v___x_406_ = l_Lean_instBEqMessageSeverity_beq(v_severity_264_, v___x_388_);
if (v___x_406_ == 0)
{
v___y_394_ = v___x_406_;
goto v___jp_393_;
}
else
{
uint8_t v___x_407_; 
lean_inc_ref(v_msgData_263_);
v___x_407_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_263_);
v___y_394_ = v___x_407_;
goto v___jp_393_;
}
v___jp_269_:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Elab_Command_getScope___redArg(v___y_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v_currNamespace_280_; lean_object* v___x_281_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v_currNamespace_280_ = lean_ctor_get(v_a_279_, 2);
lean_inc(v_currNamespace_280_);
lean_dec(v_a_279_);
v___x_281_ = l_Lean_Elab_Command_getScope___redArg(v___y_277_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_317_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_317_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_317_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_317_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_openDecls_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_env_291_; lean_object* v_messages_292_; lean_object* v_scopes_293_; lean_object* v_usedQuotCtxts_294_; lean_object* v_nextMacroScope_295_; lean_object* v_maxRecDepth_296_; lean_object* v_ngen_297_; lean_object* v_auxDeclNGen_298_; lean_object* v_infoState_299_; lean_object* v_traceState_300_; lean_object* v_snapshotTasks_301_; lean_object* v_prevLinterStates_302_; lean_object* v_codeQualityEntryTasks_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_316_; 
v_openDecls_286_ = lean_ctor_get(v_a_282_, 3);
lean_inc(v_openDecls_286_);
lean_dec(v_a_282_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v_currNamespace_280_);
lean_ctor_set(v___x_287_, 1, v_openDecls_286_);
v___x_288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___y_275_);
lean_inc_ref(v___y_273_);
lean_inc_ref(v___y_276_);
v___x_289_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_289_, 0, v___y_276_);
lean_ctor_set(v___x_289_, 1, v___y_271_);
lean_ctor_set(v___x_289_, 2, v___y_274_);
lean_ctor_set(v___x_289_, 3, v___y_273_);
lean_ctor_set(v___x_289_, 4, v___x_288_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*5, v___y_272_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*5 + 1, v___y_270_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*5 + 2, v_isSilent_265_);
v___x_290_ = lean_st_ref_take(v___y_277_);
v_env_291_ = lean_ctor_get(v___x_290_, 0);
v_messages_292_ = lean_ctor_get(v___x_290_, 1);
v_scopes_293_ = lean_ctor_get(v___x_290_, 2);
v_usedQuotCtxts_294_ = lean_ctor_get(v___x_290_, 3);
v_nextMacroScope_295_ = lean_ctor_get(v___x_290_, 4);
v_maxRecDepth_296_ = lean_ctor_get(v___x_290_, 5);
v_ngen_297_ = lean_ctor_get(v___x_290_, 6);
v_auxDeclNGen_298_ = lean_ctor_get(v___x_290_, 7);
v_infoState_299_ = lean_ctor_get(v___x_290_, 8);
v_traceState_300_ = lean_ctor_get(v___x_290_, 9);
v_snapshotTasks_301_ = lean_ctor_get(v___x_290_, 10);
v_prevLinterStates_302_ = lean_ctor_get(v___x_290_, 11);
v_codeQualityEntryTasks_303_ = lean_ctor_get(v___x_290_, 12);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_316_ == 0)
{
v___x_305_ = v___x_290_;
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_codeQualityEntryTasks_303_);
lean_inc(v_prevLinterStates_302_);
lean_inc(v_snapshotTasks_301_);
lean_inc(v_traceState_300_);
lean_inc(v_infoState_299_);
lean_inc(v_auxDeclNGen_298_);
lean_inc(v_ngen_297_);
lean_inc(v_maxRecDepth_296_);
lean_inc(v_nextMacroScope_295_);
lean_inc(v_usedQuotCtxts_294_);
lean_inc(v_scopes_293_);
lean_inc(v_messages_292_);
lean_inc(v_env_291_);
lean_dec(v___x_290_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_box(0);
v___x_308_ = l_Lean_MessageLog_add(v___x_289_, v_messages_292_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_env_291_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_scopes_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_usedQuotCtxts_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_nextMacroScope_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 5, v_maxRecDepth_296_);
lean_ctor_set(v_reuseFailAlloc_315_, 6, v_ngen_297_);
lean_ctor_set(v_reuseFailAlloc_315_, 7, v_auxDeclNGen_298_);
lean_ctor_set(v_reuseFailAlloc_315_, 8, v_infoState_299_);
lean_ctor_set(v_reuseFailAlloc_315_, 9, v_traceState_300_);
lean_ctor_set(v_reuseFailAlloc_315_, 10, v_snapshotTasks_301_);
lean_ctor_set(v_reuseFailAlloc_315_, 11, v_prevLinterStates_302_);
lean_ctor_set(v_reuseFailAlloc_315_, 12, v_codeQualityEntryTasks_303_);
v___x_310_ = v_reuseFailAlloc_315_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_st_ref_put(v___y_277_, v___x_310_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_307_);
v___x_313_ = v___x_284_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_307_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_currNamespace_280_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_271_);
v_a_318_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_281_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_281_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_271_);
v_a_326_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_278_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_278_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
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
v___jp_334_:
{
lean_object* v_fileName_340_; lean_object* v_fileMap_341_; uint8_t v_suppressElabErrors_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_361_; 
v_fileName_340_ = lean_ctor_get(v___y_266_, 0);
v_fileMap_341_ = lean_ctor_get(v___y_266_, 1);
v_suppressElabErrors_342_ = lean_ctor_get_uint8(v___y_266_, sizeof(void*)*10);
v___x_343_ = lean_box(v_suppressElabErrors_342_);
v___x_344_ = lean_box(v___y_335_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed), 3, 2);
lean_closure_set(v___f_345_, 0, v___x_343_);
lean_closure_set(v___f_345_, 1, v___x_344_);
v___x_346_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_263_);
v___x_347_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v___x_346_, v___y_267_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_361_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_361_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_361_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_inc_ref_n(v_fileMap_341_, 2);
v___x_352_ = l_Lean_FileMap_toPosition(v_fileMap_341_, v___y_338_);
lean_dec(v___y_338_);
v___x_353_ = l_Lean_FileMap_toPosition(v_fileMap_341_, v___y_339_);
lean_dec(v___y_339_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
v___x_355_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___closed__0));
if (v_suppressElabErrors_342_ == 0)
{
lean_del_object(v___x_350_);
lean_dec_ref(v___f_345_);
v___y_270_ = v___y_336_;
v___y_271_ = v___x_352_;
v___y_272_ = v___y_337_;
v___y_273_ = v___x_355_;
v___y_274_ = v___x_354_;
v___y_275_ = v_a_348_;
v___y_276_ = v_fileName_340_;
v___y_277_ = v___y_267_;
goto v___jp_269_;
}
else
{
uint8_t v___x_356_; 
lean_inc(v_a_348_);
v___x_356_ = l_Lean_MessageData_hasTag(v___f_345_, v_a_348_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec_ref_known(v___x_354_, 1);
lean_dec_ref(v___x_352_);
lean_dec(v_a_348_);
v___x_357_ = lean_box(0);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_357_);
v___x_359_ = v___x_350_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_del_object(v___x_350_);
v___y_270_ = v___y_336_;
v___y_271_ = v___x_352_;
v___y_272_ = v___y_337_;
v___y_273_ = v___x_355_;
v___y_274_ = v___x_354_;
v___y_275_ = v_a_348_;
v___y_276_ = v_fileName_340_;
v___y_277_ = v___y_267_;
goto v___jp_269_;
}
}
}
}
v___jp_362_:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Syntax_getTailPos_x3f(v___y_366_, v___y_365_);
lean_dec(v___y_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_inc(v___y_367_);
v___y_335_ = v___y_363_;
v___y_336_ = v___y_364_;
v___y_337_ = v___y_365_;
v___y_338_ = v___y_367_;
v___y_339_ = v___y_367_;
goto v___jp_334_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_368_, 1);
v___y_335_ = v___y_363_;
v___y_336_ = v___y_364_;
v___y_337_ = v___y_365_;
v___y_338_ = v___y_367_;
v___y_339_ = v_val_369_;
goto v___jp_334_;
}
}
v___jp_370_:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Elab_Command_getRef___redArg(v___y_266_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v_ref_376_; lean_object* v___x_377_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v_ref_376_ = l_Lean_replaceRef(v_ref_262_, v_a_375_);
lean_dec(v_a_375_);
v___x_377_ = l_Lean_Syntax_getPos_x3f(v_ref_376_, v___y_372_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___y_363_ = v___y_371_;
v___y_364_ = v___y_373_;
v___y_365_ = v___y_372_;
v___y_366_ = v_ref_376_;
v___y_367_ = v___x_378_;
goto v___jp_362_;
}
else
{
lean_object* v_val_379_; 
v_val_379_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_val_379_);
lean_dec_ref_known(v___x_377_, 1);
v___y_363_ = v___y_371_;
v___y_364_ = v___y_373_;
v___y_365_ = v___y_372_;
v___y_366_ = v_ref_376_;
v___y_367_ = v_val_379_;
goto v___jp_362_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_msgData_263_);
v_a_380_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_374_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_374_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
v___jp_389_:
{
if (v___y_392_ == 0)
{
v___y_371_ = v___y_390_;
v___y_372_ = v___y_391_;
v___y_373_ = v_severity_264_;
goto v___jp_370_;
}
else
{
v___y_371_ = v___y_390_;
v___y_372_ = v___y_391_;
v___y_373_ = v___x_388_;
goto v___jp_370_;
}
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_scopes_397_; lean_object* v___x_398_; lean_object* v_opts_399_; uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_395_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_396_ = lean_st_ref_get(v___y_267_);
v_scopes_397_ = lean_ctor_get(v___x_396_, 2);
lean_inc(v_scopes_397_);
lean_dec(v___x_396_);
v___x_398_ = l_List_head_x21___redArg(v___x_395_, v_scopes_397_);
lean_dec(v_scopes_397_);
v_opts_399_ = lean_ctor_get(v___x_398_, 1);
lean_inc_ref(v_opts_399_);
lean_dec(v___x_398_);
v___x_400_ = 1;
v___x_401_ = l_Lean_instBEqMessageSeverity_beq(v_severity_264_, v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_opts_399_);
v___y_390_ = v___y_394_;
v___y_391_ = v___y_394_;
v___y_392_ = v___x_401_;
goto v___jp_389_;
}
else
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = l_Lean_warningAsError;
v___x_403_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_399_, v___x_402_);
lean_dec_ref(v_opts_399_);
v___y_390_ = v___y_394_;
v___y_391_ = v___y_394_;
v___y_392_ = v___x_403_;
goto v___jp_389_;
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_msgData_263_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___boxed(lean_object* v_ref_408_, lean_object* v_msgData_409_, lean_object* v_severity_410_, lean_object* v_isSilent_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v_severity_boxed_415_; uint8_t v_isSilent_boxed_416_; lean_object* v_res_417_; 
v_severity_boxed_415_ = lean_unbox(v_severity_410_);
v_isSilent_boxed_416_ = lean_unbox(v_isSilent_411_);
v_res_417_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(v_ref_408_, v_msgData_409_, v_severity_boxed_415_, v_isSilent_boxed_416_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v_ref_408_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(lean_object* v_ref_418_, lean_object* v_msgData_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v___x_423_ = 1;
v___x_424_ = 0;
v___x_425_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(v_ref_418_, v_msgData_419_, v___x_423_, v___x_424_, v___y_420_, v___y_421_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15___boxed(lean_object* v_ref_426_, lean_object* v_msgData_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(v_ref_426_, v_msgData_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v_ref_426_);
return v_res_431_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__0));
v___x_434_ = l_Lean_stringToMessageData(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__2));
v___x_437_ = l_Lean_stringToMessageData(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(lean_object* v_linterOption_438_, lean_object* v_stx_439_, lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_name_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_462_; 
v_name_444_ = lean_ctor_get(v_linterOption_438_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_linterOption_438_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v_linterOption_438_, 1);
lean_dec(v_unused_463_);
v___x_446_ = v_linterOption_438_;
v_isShared_447_ = v_isSharedCheck_462_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_name_444_);
lean_dec(v_linterOption_438_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_462_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1);
lean_inc(v_name_444_);
v___x_449_ = l_Lean_MessageData_ofName(v_name_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 7);
lean_ctor_set(v___x_446_, 1, v___x_449_);
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_461_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_disable_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_452_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v_disable_454_ = l_Lean_MessageData_note(v___x_453_);
v___x_455_ = l_Lean_Linter_linterMessageTag;
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v_msg_440_);
lean_ctor_set(v___x_456_, 1, v_disable_454_);
v___x_457_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_458_, 0, v_name_444_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
lean_inc(v_stx_439_);
v___x_459_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_459_, 0, v_stx_439_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(v_stx_439_, v___x_459_, v___y_441_, v___y_442_);
lean_dec(v_stx_439_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object* v_linterOption_464_, lean_object* v_stx_465_, lean_object* v_msg_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_linterOption_464_, v_stx_465_, v_msg_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(lean_object* v_o_473_, lean_object* v_k_474_, uint8_t v_v_475_){
_start:
{
lean_object* v_map_476_; uint8_t v_hasTrace_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_491_; 
v_map_476_ = lean_ctor_get(v_o_473_, 0);
v_hasTrace_477_ = lean_ctor_get_uint8(v_o_473_, sizeof(void*)*1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_o_473_);
if (v_isSharedCheck_491_ == 0)
{
v___x_479_ = v_o_473_;
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_map_476_);
lean_dec(v_o_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_481_, 0, v_v_475_);
lean_inc(v_k_474_);
v___x_482_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_474_, v___x_481_, v_map_476_);
if (v_hasTrace_477_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_486_; 
v___x_483_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___closed__0));
v___x_484_ = l_Lean_Name_isPrefixOf(v___x_483_, v_k_474_);
lean_dec(v_k_474_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_486_ = v___x_479_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_482_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_484_);
return v___x_486_;
}
}
else
{
lean_object* v___x_489_; 
lean_dec(v_k_474_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_489_ = v___x_479_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*1, v_hasTrace_477_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___boxed(lean_object* v_o_492_, lean_object* v_k_493_, lean_object* v_v_494_){
_start:
{
uint8_t v_v_boxed_495_; lean_object* v_res_496_; 
v_v_boxed_495_ = lean_unbox(v_v_494_);
v_res_496_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(v_o_492_, v_k_493_, v_v_boxed_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object* v_opts_497_, lean_object* v_opt_498_, uint8_t v_val_499_){
_start:
{
lean_object* v_name_500_; lean_object* v___x_501_; 
v_name_500_ = lean_ctor_get(v_opt_498_, 0);
lean_inc(v_name_500_);
lean_dec_ref(v_opt_498_);
v___x_501_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(v_opts_497_, v_name_500_, v_val_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object* v_opts_502_, lean_object* v_opt_503_, lean_object* v_val_504_){
_start:
{
uint8_t v_val_boxed_505_; lean_object* v_res_506_; 
v_val_boxed_505_ = lean_unbox(v_val_504_);
v_res_506_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_opts_502_, v_opt_503_, v_val_boxed_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_i_509_, lean_object* v_k_510_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_array_get_size(v_keys_507_);
v___x_512_ = lean_nat_dec_lt(v_i_509_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_i_509_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v_k_x27_514_; uint8_t v___x_515_; 
v_k_x27_514_ = lean_array_fget_borrowed(v_keys_507_, v_i_509_);
v___x_515_ = lean_name_eq(v_k_510_, v_k_x27_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_i_509_, v___x_516_);
lean_dec(v_i_509_);
v_i_509_ = v___x_517_;
goto _start;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_array_fget_borrowed(v_vals_508_, v_i_509_);
lean_dec(v_i_509_);
lean_inc(v___x_519_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_521_, lean_object* v_vals_522_, lean_object* v_i_523_, lean_object* v_k_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_521_, v_vals_522_, v_i_523_, v_k_524_);
lean_dec(v_k_524_);
lean_dec_ref(v_vals_522_);
lean_dec_ref(v_keys_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(lean_object* v_x_526_, size_t v_x_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_es_529_; lean_object* v___x_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v_j_533_; lean_object* v___x_534_; 
v_es_529_ = lean_ctor_get(v_x_526_, 0);
v___x_530_ = lean_box(2);
v___x_531_ = ((size_t)31ULL);
v___x_532_ = lean_usize_land(v_x_527_, v___x_531_);
v_j_533_ = lean_usize_to_nat(v___x_532_);
v___x_534_ = lean_array_get_borrowed(v___x_530_, v_es_529_, v_j_533_);
lean_dec(v_j_533_);
switch(lean_obj_tag(v___x_534_))
{
case 0:
{
lean_object* v_key_535_; lean_object* v_val_536_; uint8_t v___x_537_; 
v_key_535_ = lean_ctor_get(v___x_534_, 0);
v_val_536_ = lean_ctor_get(v___x_534_, 1);
v___x_537_ = lean_name_eq(v_x_528_, v_key_535_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(0);
return v___x_538_;
}
else
{
lean_object* v___x_539_; 
lean_inc(v_val_536_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_val_536_);
return v___x_539_;
}
}
case 1:
{
lean_object* v_node_540_; size_t v___x_541_; size_t v___x_542_; 
v_node_540_ = lean_ctor_get(v___x_534_, 0);
v___x_541_ = ((size_t)5ULL);
v___x_542_ = lean_usize_shift_right(v_x_527_, v___x_541_);
v_x_526_ = v_node_540_;
v_x_527_ = v___x_542_;
goto _start;
}
default: 
{
lean_object* v___x_544_; 
v___x_544_ = lean_box(0);
return v___x_544_;
}
}
}
else
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_ks_545_ = lean_ctor_get(v_x_526_, 0);
v_vs_546_ = lean_ctor_get(v_x_526_, 1);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_545_, v_vs_546_, v___x_547_, v_x_528_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
size_t v_x_26395__boxed_552_; lean_object* v_res_553_; 
v_x_26395__boxed_552_ = lean_unbox_usize(v_x_550_);
lean_dec(v_x_550_);
v_res_553_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_549_, v_x_26395__boxed_552_, v_x_551_);
lean_dec(v_x_551_);
lean_dec_ref(v_x_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
uint64_t v___y_557_; 
if (lean_obj_tag(v_x_555_) == 0)
{
uint64_t v___x_560_; 
v___x_560_ = 1723ULL;
v___y_557_ = v___x_560_;
goto v___jp_556_;
}
else
{
uint64_t v_hash_561_; 
v_hash_561_ = lean_ctor_get_uint64(v_x_555_, sizeof(void*)*2);
v___y_557_ = v_hash_561_;
goto v___jp_556_;
}
v___jp_556_:
{
size_t v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_uint64_to_usize(v___y_557_);
v___x_559_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_554_, v___x_558_, v_x_555_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg___boxed(lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_x_562_, v_x_563_);
lean_dec(v_x_563_);
lean_dec_ref(v_x_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v_ks_569_; lean_object* v_vs_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_594_; 
v_ks_569_ = lean_ctor_get(v_x_565_, 0);
v_vs_570_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_594_ == 0)
{
v___x_572_ = v_x_565_;
v_isShared_573_ = v_isSharedCheck_594_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_vs_570_);
lean_inc(v_ks_569_);
lean_dec(v_x_565_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_594_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_array_get_size(v_ks_569_);
v___x_575_ = lean_nat_dec_lt(v_x_566_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
lean_dec(v_x_566_);
v___x_576_ = lean_array_push(v_ks_569_, v_x_567_);
v___x_577_ = lean_array_push(v_vs_570_, v_x_568_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_577_);
lean_ctor_set(v___x_572_, 0, v___x_576_);
v___x_579_ = v___x_572_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
else
{
lean_object* v_k_x27_581_; uint8_t v___x_582_; 
v_k_x27_581_ = lean_array_fget_borrowed(v_ks_569_, v_x_566_);
v___x_582_ = lean_name_eq(v_x_567_, v_k_x27_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_584_; 
if (v_isShared_573_ == 0)
{
v___x_584_ = v___x_572_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_ks_569_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_vs_570_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v_x_566_, v___x_585_);
lean_dec(v_x_566_);
v_x_565_ = v___x_584_;
v_x_566_ = v___x_586_;
goto _start;
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_589_ = lean_array_fset(v_ks_569_, v_x_566_, v_x_567_);
v___x_590_ = lean_array_fset(v_vs_570_, v_x_566_, v_x_568_);
lean_dec(v_x_566_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_590_);
lean_ctor_set(v___x_572_, 0, v___x_589_);
v___x_592_ = v___x_572_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(lean_object* v_n_595_, lean_object* v_k_596_, lean_object* v_v_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(v_n_595_, v___x_598_, v_k_596_, v_v_597_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(lean_object* v_x_601_, size_t v_x_602_, size_t v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v_es_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v_j_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_es_606_ = lean_ctor_get(v_x_601_, 0);
v___x_607_ = ((size_t)31ULL);
v___x_608_ = lean_usize_land(v_x_602_, v___x_607_);
v_j_609_ = lean_usize_to_nat(v___x_608_);
v___x_610_ = lean_array_get_size(v_es_606_);
v___x_611_ = lean_nat_dec_lt(v_j_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_j_609_);
lean_dec(v_x_605_);
lean_dec(v_x_604_);
return v_x_601_;
}
else
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_650_; 
lean_inc_ref(v_es_606_);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_x_601_, 0);
lean_dec(v_unused_651_);
v___x_613_ = v_x_601_;
v_isShared_614_ = v_isSharedCheck_650_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_x_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_650_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_v_615_; lean_object* v___x_616_; lean_object* v_xs_x27_617_; lean_object* v___y_619_; 
v_v_615_ = lean_array_fget(v_es_606_, v_j_609_);
v___x_616_ = lean_box(0);
v_xs_x27_617_ = lean_array_fset(v_es_606_, v_j_609_, v___x_616_);
switch(lean_obj_tag(v_v_615_))
{
case 0:
{
lean_object* v_key_624_; lean_object* v_val_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_635_; 
v_key_624_ = lean_ctor_get(v_v_615_, 0);
v_val_625_ = lean_ctor_get(v_v_615_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_v_615_);
if (v_isSharedCheck_635_ == 0)
{
v___x_627_ = v_v_615_;
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_val_625_);
lean_inc(v_key_624_);
lean_dec(v_v_615_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
uint8_t v___x_629_; 
v___x_629_ = lean_name_eq(v_x_604_, v_key_624_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_del_object(v___x_627_);
v___x_630_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_624_, v_val_625_, v_x_604_, v_x_605_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___y_619_ = v___x_631_;
goto v___jp_618_;
}
else
{
lean_object* v___x_633_; 
lean_dec(v_val_625_);
lean_dec(v_key_624_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_x_605_);
lean_ctor_set(v___x_627_, 0, v_x_604_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_x_604_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_x_605_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
v___y_619_ = v___x_633_;
goto v___jp_618_;
}
}
}
}
case 1:
{
lean_object* v_node_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_648_; 
v_node_636_ = lean_ctor_get(v_v_615_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_v_615_);
if (v_isSharedCheck_648_ == 0)
{
v___x_638_ = v_v_615_;
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_node_636_);
lean_dec(v_v_615_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_640_ = ((size_t)5ULL);
v___x_641_ = lean_usize_shift_right(v_x_602_, v___x_640_);
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_add(v_x_603_, v___x_642_);
v___x_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_node_636_, v___x_641_, v___x_643_, v_x_604_, v_x_605_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_644_);
v___x_646_ = v___x_638_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v___y_619_ = v___x_646_;
goto v___jp_618_;
}
}
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v_x_604_);
lean_ctor_set(v___x_649_, 1, v_x_605_);
v___y_619_ = v___x_649_;
goto v___jp_618_;
}
}
v___jp_618_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = lean_array_fset(v_xs_x27_617_, v_j_609_, v___y_619_);
lean_dec(v_j_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_620_);
v___x_622_ = v___x_613_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v_ks_652_; lean_object* v_vs_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_671_; 
v_ks_652_ = lean_ctor_get(v_x_601_, 0);
v_vs_653_ = lean_ctor_get(v_x_601_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_671_ == 0)
{
v___x_655_ = v_x_601_;
v_isShared_656_ = v_isSharedCheck_671_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_vs_653_);
lean_inc(v_ks_652_);
lean_dec(v_x_601_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_671_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_ks_652_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_vs_653_);
v___x_658_ = v_reuseFailAlloc_670_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v_newNode_659_; size_t v___x_660_; uint8_t v___x_661_; 
v_newNode_659_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(v___x_658_, v_x_604_, v_x_605_);
v___x_660_ = ((size_t)7ULL);
v___x_661_ = lean_usize_dec_le(v___x_660_, v_x_603_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_659_);
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
lean_dec(v___x_662_);
if (v___x_664_ == 0)
{
lean_object* v_ks_665_; lean_object* v_vs_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_ks_665_ = lean_ctor_get(v_newNode_659_, 0);
lean_inc_ref(v_ks_665_);
v_vs_666_ = lean_ctor_get(v_newNode_659_, 1);
lean_inc_ref(v_vs_666_);
lean_dec_ref(v_newNode_659_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0);
v___x_669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_x_603_, v_ks_665_, v_vs_666_, v___x_667_, v___x_668_);
lean_dec_ref(v_vs_666_);
lean_dec_ref(v_ks_665_);
return v___x_669_;
}
else
{
return v_newNode_659_;
}
}
else
{
return v_newNode_659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(size_t v_depth_672_, lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_i_675_, lean_object* v_entries_676_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_array_get_size(v_keys_673_);
v___x_678_ = lean_nat_dec_lt(v_i_675_, v___x_677_);
if (v___x_678_ == 0)
{
lean_dec(v_i_675_);
return v_entries_676_;
}
else
{
lean_object* v_k_679_; lean_object* v_v_680_; uint64_t v___y_682_; 
v_k_679_ = lean_array_fget_borrowed(v_keys_673_, v_i_675_);
v_v_680_ = lean_array_fget_borrowed(v_vals_674_, v_i_675_);
if (lean_obj_tag(v_k_679_) == 0)
{
uint64_t v___x_693_; 
v___x_693_ = 1723ULL;
v___y_682_ = v___x_693_;
goto v___jp_681_;
}
else
{
uint64_t v_hash_694_; 
v_hash_694_ = lean_ctor_get_uint64(v_k_679_, sizeof(void*)*2);
v___y_682_ = v_hash_694_;
goto v___jp_681_;
}
v___jp_681_:
{
size_t v_h_683_; size_t v___x_684_; lean_object* v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v_h_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_h_683_ = lean_uint64_to_usize(v___y_682_);
v___x_684_ = ((size_t)5ULL);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_sub(v_depth_672_, v___x_686_);
v___x_688_ = lean_usize_mul(v___x_684_, v___x_687_);
v_h_689_ = lean_usize_shift_right(v_h_683_, v___x_688_);
v___x_690_ = lean_nat_add(v_i_675_, v___x_685_);
lean_dec(v_i_675_);
lean_inc(v_v_680_);
lean_inc(v_k_679_);
v___x_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_entries_676_, v_h_689_, v_depth_672_, v_k_679_, v_v_680_);
v_i_675_ = v___x_690_;
v_entries_676_ = v___x_691_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg___boxed(lean_object* v_depth_695_, lean_object* v_keys_696_, lean_object* v_vals_697_, lean_object* v_i_698_, lean_object* v_entries_699_){
_start:
{
size_t v_depth_boxed_700_; lean_object* v_res_701_; 
v_depth_boxed_700_ = lean_unbox_usize(v_depth_695_);
lean_dec(v_depth_695_);
v_res_701_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_depth_boxed_700_, v_keys_696_, v_vals_697_, v_i_698_, v_entries_699_);
lean_dec_ref(v_vals_697_);
lean_dec_ref(v_keys_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
size_t v_x_26536__boxed_707_; size_t v_x_26537__boxed_708_; lean_object* v_res_709_; 
v_x_26536__boxed_707_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_x_26537__boxed_708_ = lean_unbox_usize(v_x_704_);
lean_dec(v_x_704_);
v_res_709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_702_, v_x_26536__boxed_707_, v_x_26537__boxed_708_, v_x_705_, v_x_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint64_t v___y_714_; 
if (lean_obj_tag(v_x_711_) == 0)
{
uint64_t v___x_718_; 
v___x_718_ = 1723ULL;
v___y_714_ = v___x_718_;
goto v___jp_713_;
}
else
{
uint64_t v_hash_719_; 
v_hash_719_ = lean_ctor_get_uint64(v_x_711_, sizeof(void*)*2);
v___y_714_ = v_hash_719_;
goto v___jp_713_;
}
v___jp_713_:
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_uint64_to_usize(v___y_714_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_710_, v___x_715_, v___x_716_, v_x_711_, v_x_712_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(lean_object* v_oldCounters_720_, lean_object* v_x_721_, lean_object* v_____s_722_){
_start:
{
lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___x_725_; 
v_fst_723_ = lean_ctor_get(v_x_721_, 0);
lean_inc(v_fst_723_);
v_snd_724_ = lean_ctor_get(v_x_721_, 1);
lean_inc(v_snd_724_);
lean_dec_ref(v_x_721_);
v___x_725_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_oldCounters_720_, v_fst_723_);
if (lean_obj_tag(v___x_725_) == 1)
{
lean_object* v_val_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_735_; 
v_val_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_val_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v_result_731_; lean_object* v___x_733_; 
v___x_730_ = lean_nat_sub(v_snd_724_, v_val_726_);
lean_dec(v_val_726_);
lean_dec(v_snd_724_);
v_result_731_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_____s_722_, v_fst_723_, v___x_730_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_result_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_result_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v_result_736_; lean_object* v___x_737_; 
lean_dec(v___x_725_);
v_result_736_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_____s_722_, v_fst_723_, v_snd_724_);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v_result_736_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed(lean_object* v_oldCounters_738_, lean_object* v_x_739_, lean_object* v_____s_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(v_oldCounters_738_, v_x_739_, v_____s_740_);
lean_dec_ref(v_oldCounters_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0(lean_object* v_f_742_, lean_object* v_s_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_a_744_);
lean_ctor_set(v___x_746_, 1, v_b_745_);
v___x_747_ = lean_apply_2(v_f_742_, v___x_746_, v_s_743_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
v_a_756_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_747_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_747_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(lean_object* v_f_764_, lean_object* v_keys_765_, lean_object* v_vals_766_, lean_object* v_i_767_, lean_object* v_acc_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_array_get_size(v_keys_765_);
v___x_770_ = lean_nat_dec_lt(v_i_767_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec(v_i_767_);
lean_dec_ref(v_f_764_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v_acc_768_);
return v___x_771_;
}
else
{
lean_object* v_k_772_; lean_object* v_v_773_; lean_object* v___x_774_; 
v_k_772_ = lean_array_fget_borrowed(v_keys_765_, v_i_767_);
v_v_773_ = lean_array_fget_borrowed(v_vals_766_, v_i_767_);
lean_inc_ref(v_f_764_);
lean_inc(v_v_773_);
lean_inc(v_k_772_);
v___x_774_ = lean_apply_3(v_f_764_, v_acc_768_, v_k_772_, v_v_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec(v_i_767_);
lean_dec_ref(v_f_764_);
return v___x_774_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_add(v_i_767_, v___x_776_);
lean_dec(v_i_767_);
v_i_767_ = v___x_777_;
v_acc_768_ = v_a_775_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg___boxed(lean_object* v_f_779_, lean_object* v_keys_780_, lean_object* v_vals_781_, lean_object* v_i_782_, lean_object* v_acc_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_779_, v_keys_780_, v_vals_781_, v_i_782_, v_acc_783_);
lean_dec_ref(v_vals_781_);
lean_dec_ref(v_keys_780_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(lean_object* v_f_785_, lean_object* v_as_786_, size_t v_i_787_, size_t v_stop_788_, lean_object* v_b_789_){
_start:
{
lean_object* v_a_791_; lean_object* v___y_796_; uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_eq(v_i_787_, v_stop_788_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_array_uget_borrowed(v_as_786_, v_i_787_);
switch(lean_obj_tag(v___x_799_))
{
case 0:
{
lean_object* v_key_800_; lean_object* v_val_801_; lean_object* v___x_802_; 
v_key_800_ = lean_ctor_get(v___x_799_, 0);
v_val_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc_ref(v_f_785_);
lean_inc(v_val_801_);
lean_inc(v_key_800_);
v___x_802_ = lean_apply_3(v_f_785_, v_b_789_, v_key_800_, v_val_801_);
v___y_796_ = v___x_802_;
goto v___jp_795_;
}
case 1:
{
lean_object* v_node_803_; lean_object* v___x_804_; 
v_node_803_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_node_803_);
lean_inc_ref(v_f_785_);
v___x_804_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_785_, v_node_803_, v_b_789_);
v___y_796_ = v___x_804_;
goto v___jp_795_;
}
default: 
{
v_a_791_ = v_b_789_;
goto v___jp_790_;
}
}
}
else
{
lean_object* v___x_805_; 
lean_dec_ref(v_f_785_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_b_789_);
return v___x_805_;
}
v___jp_790_:
{
size_t v___x_792_; size_t v___x_793_; 
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_787_, v___x_792_);
v_i_787_ = v___x_793_;
v_b_789_ = v_a_791_;
goto _start;
}
v___jp_795_:
{
if (lean_obj_tag(v___y_796_) == 0)
{
lean_dec_ref(v_f_785_);
return v___y_796_;
}
else
{
lean_object* v_a_797_; 
v_a_797_ = lean_ctor_get(v___y_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___y_796_, 1);
v_a_791_ = v_a_797_;
goto v___jp_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(lean_object* v_f_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v_es_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_822_; 
v_es_809_ = lean_ctor_get(v_x_807_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_822_ == 0)
{
v___x_811_ = v_x_807_;
v_isShared_812_ = v_isSharedCheck_822_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_es_809_);
lean_dec(v_x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_822_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_array_get_size(v_es_809_);
v___x_815_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_817_; 
lean_dec_ref(v_es_809_);
lean_dec_ref(v_f_806_);
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 1);
lean_ctor_set(v___x_811_, 0, v_x_808_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_x_808_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
lean_del_object(v___x_811_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = lean_usize_of_nat(v___x_814_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_806_, v_es_809_, v___x_819_, v___x_820_, v_x_808_);
lean_dec_ref(v_es_809_);
return v___x_821_;
}
}
}
else
{
lean_object* v_ks_823_; lean_object* v_vs_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_ks_823_ = lean_ctor_get(v_x_807_, 0);
lean_inc_ref(v_ks_823_);
v_vs_824_ = lean_ctor_get(v_x_807_, 1);
lean_inc_ref(v_vs_824_);
lean_dec_ref_known(v_x_807_, 2);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_806_, v_ks_823_, v_vs_824_, v___x_825_, v_x_808_);
lean_dec_ref(v_vs_824_);
lean_dec_ref(v_ks_823_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg___boxed(lean_object* v_f_827_, lean_object* v_as_828_, lean_object* v_i_829_, lean_object* v_stop_830_, lean_object* v_b_831_){
_start:
{
size_t v_i_boxed_832_; size_t v_stop_boxed_833_; lean_object* v_res_834_; 
v_i_boxed_832_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v_stop_boxed_833_ = lean_unbox_usize(v_stop_830_);
lean_dec(v_stop_830_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_827_, v_as_828_, v_i_boxed_832_, v_stop_boxed_833_, v_b_831_);
lean_dec_ref(v_as_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(lean_object* v_map_835_, lean_object* v_init_836_, lean_object* v_f_837_){
_start:
{
lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v_a_840_; 
v___f_838_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0), 4, 1);
lean_closure_set(v___f_838_, 0, v_f_837_);
lean_inc_ref(v_map_835_);
v___x_839_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v___f_838_, v_map_835_, v_init_836_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
return v_a_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___boxed(lean_object* v_map_841_, lean_object* v_init_842_, lean_object* v_f_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_map_841_, v_init_842_, v_f_843_);
lean_dec_ref(v_map_841_);
return v_res_844_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0(void){
_start:
{
lean_object* v___x_845_; lean_object* v_result_846_; 
v___x_845_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v_result_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_result_846_, 0, v___x_845_);
return v_result_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object* v_newCounters_847_, lean_object* v_oldCounters_848_){
_start:
{
lean_object* v___f_849_; lean_object* v_result_850_; lean_object* v___x_851_; 
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed), 3, 1);
lean_closure_set(v___f_849_, 0, v_oldCounters_848_);
v_result_850_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0);
v___x_851_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_newCounters_847_, v_result_850_, v___f_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object* v_newCounters_852_, lean_object* v_oldCounters_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_newCounters_852_, v_oldCounters_853_);
lean_dec_ref(v_newCounters_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object* v___x_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
if (lean_obj_tag(v_a_856_) == 0)
{
lean_object* v___x_858_; 
lean_dec_ref(v___x_855_);
v___x_858_ = lean_array_to_list(v_a_857_);
return v___x_858_;
}
else
{
lean_object* v_head_859_; lean_object* v_tail_860_; lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v_head_859_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_head_859_);
v_tail_860_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_tail_860_);
lean_dec_ref_known(v_a_856_, 2);
v_fst_861_ = lean_ctor_get(v_head_859_, 0);
lean_inc(v_fst_861_);
v_snd_862_ = lean_ctor_get(v_head_859_, 1);
lean_inc(v_snd_862_);
lean_dec(v_head_859_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_nat_dec_lt(v___x_863_, v_snd_862_);
lean_dec(v_snd_862_);
if (v___x_864_ == 0)
{
lean_dec(v_fst_861_);
v_a_856_ = v_tail_860_;
goto _start;
}
else
{
uint8_t v___x_866_; 
lean_inc(v_fst_861_);
lean_inc_ref(v___x_855_);
v___x_866_ = l_Lean_getReducibilityStatusCore(v___x_855_, v_fst_861_);
if (v___x_866_ == 1)
{
uint8_t v___x_867_; 
lean_inc_ref(v___x_855_);
v___x_867_ = l_Lean_Meta_isInstanceCore(v___x_855_, v_fst_861_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = l_Lean_MessageData_ofConstName(v_fst_861_, v___x_867_);
v___x_869_ = lean_array_push(v_a_857_, v___x_868_);
v_a_856_ = v_tail_860_;
v_a_857_ = v___x_869_;
goto _start;
}
else
{
lean_dec(v_fst_861_);
v_a_856_ = v_tail_860_;
goto _start;
}
}
else
{
lean_dec(v_fst_861_);
v_a_856_ = v_tail_860_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0(lean_object* v_f_873_, lean_object* v_x1_874_, lean_object* v_x2_875_, lean_object* v_x3_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_apply_3(v_f_873_, v_x1_874_, v_x2_875_, v_x3_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(lean_object* v_f_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_i_881_, lean_object* v_acc_882_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_array_get_size(v_keys_879_);
v___x_884_ = lean_nat_dec_lt(v_i_881_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec(v_i_881_);
lean_dec(v_f_878_);
return v_acc_882_;
}
else
{
lean_object* v_k_885_; lean_object* v_v_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_k_885_ = lean_array_fget_borrowed(v_keys_879_, v_i_881_);
v_v_886_ = lean_array_fget_borrowed(v_vals_880_, v_i_881_);
lean_inc(v_f_878_);
lean_inc(v_v_886_);
lean_inc(v_k_885_);
v___x_887_ = lean_apply_3(v_f_878_, v_acc_882_, v_k_885_, v_v_886_);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_i_881_, v___x_888_);
lean_dec(v_i_881_);
v_i_881_ = v___x_889_;
v_acc_882_ = v___x_887_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg___boxed(lean_object* v_f_891_, lean_object* v_keys_892_, lean_object* v_vals_893_, lean_object* v_i_894_, lean_object* v_acc_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_891_, v_keys_892_, v_vals_893_, v_i_894_, v_acc_895_);
lean_dec_ref(v_vals_893_);
lean_dec_ref(v_keys_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(lean_object* v_f_897_, lean_object* v_as_898_, size_t v_i_899_, size_t v_stop_900_, lean_object* v_b_901_){
_start:
{
lean_object* v___y_903_; uint8_t v___x_907_; 
v___x_907_ = lean_usize_dec_eq(v_i_899_, v_stop_900_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
v___x_908_ = lean_array_uget_borrowed(v_as_898_, v_i_899_);
switch(lean_obj_tag(v___x_908_))
{
case 0:
{
lean_object* v_key_909_; lean_object* v_val_910_; lean_object* v___x_911_; 
v_key_909_ = lean_ctor_get(v___x_908_, 0);
v_val_910_ = lean_ctor_get(v___x_908_, 1);
lean_inc(v_f_897_);
lean_inc(v_val_910_);
lean_inc(v_key_909_);
v___x_911_ = lean_apply_3(v_f_897_, v_b_901_, v_key_909_, v_val_910_);
v___y_903_ = v___x_911_;
goto v___jp_902_;
}
case 1:
{
lean_object* v_node_912_; lean_object* v___x_913_; 
v_node_912_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_f_897_);
v___x_913_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_897_, v_node_912_, v_b_901_);
v___y_903_ = v___x_913_;
goto v___jp_902_;
}
default: 
{
v___y_903_ = v_b_901_;
goto v___jp_902_;
}
}
}
else
{
lean_dec(v_f_897_);
return v_b_901_;
}
v___jp_902_:
{
size_t v___x_904_; size_t v___x_905_; 
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_899_, v___x_904_);
v_i_899_ = v___x_905_;
v_b_901_ = v___y_903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(lean_object* v_f_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_es_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_es_917_ = lean_ctor_get(v_x_915_, 0);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_array_get_size(v_es_917_);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_dec(v_f_914_);
return v_x_916_;
}
else
{
size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v___x_921_ = ((size_t)0ULL);
v___x_922_ = lean_usize_of_nat(v___x_919_);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_914_, v_es_917_, v___x_921_, v___x_922_, v_x_916_);
return v___x_923_;
}
}
else
{
lean_object* v_ks_924_; lean_object* v_vs_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_ks_924_ = lean_ctor_get(v_x_915_, 0);
v_vs_925_ = lean_ctor_get(v_x_915_, 1);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_914_, v_ks_924_, v_vs_925_, v___x_926_, v_x_916_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg___boxed(lean_object* v_f_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_928_, v_x_929_, v_x_930_);
lean_dec_ref(v_x_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg___boxed(lean_object* v_f_932_, lean_object* v_as_933_, lean_object* v_i_934_, lean_object* v_stop_935_, lean_object* v_b_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; lean_object* v_res_939_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_935_);
lean_dec(v_stop_935_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_932_, v_as_933_, v_i_boxed_937_, v_stop_boxed_938_, v_b_936_);
lean_dec_ref(v_as_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(lean_object* v_map_940_, lean_object* v_f_941_, lean_object* v_init_942_){
_start:
{
lean_object* v___f_943_; lean_object* v___x_944_; 
v___f_943_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0), 4, 1);
lean_closure_set(v___f_943_, 0, v_f_941_);
v___x_944_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v___f_943_, v_map_940_, v_init_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___boxed(lean_object* v_map_945_, lean_object* v_f_946_, lean_object* v_init_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_map_945_, v_f_946_, v_init_947_);
lean_dec_ref(v_map_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___lam__0(lean_object* v_ps_949_, lean_object* v_k_950_, lean_object* v_v_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_k_950_);
lean_ctor_set(v___x_952_, 1, v_v_951_);
v___x_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v_ps_949_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(lean_object* v_m_955_){
_start:
{
lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___f_956_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___closed__0));
v___x_957_ = lean_box(0);
v___x_958_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_m_955_, v___f_956_, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___boxed(lean_object* v_m_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v_m_959_);
lean_dec_ref(v_m_959_);
return v_res_960_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__0));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__2));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_box(1);
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__5));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__9));
v___x_977_ = l_Lean_MessageData_ofFormat(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__12));
v___x_982_ = l_Lean_MessageData_ofFormat(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(lean_object* v_kind_987_, lean_object* v___x_988_, lean_object* v_a_989_, uint8_t v___x_990_, lean_object* v_diag_991_, uint8_t v_a_992_, uint8_t v_val_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1049_; uint16_t v___y_1050_; lean_object* v_fileName_1051_; lean_object* v_fileMap_1052_; lean_object* v_currNamespace_1053_; lean_object* v_openDecls_1054_; lean_object* v_initHeartbeats_1055_; lean_object* v_maxHeartbeats_1056_; lean_object* v_quotContext_1057_; lean_object* v_currMacroScope_1058_; lean_object* v_cancelTk_x3f_1059_; lean_object* v_inheritedTraceOptions_1060_; lean_object* v_currRecDepth_1061_; lean_object* v_ref_1062_; uint8_t v_suppressElabErrors_1063_; uint8_t v_isRecordingDeps_1064_; lean_object* v___y_1065_; lean_object* v_toCold_1105_; lean_object* v_currRecDepth_1106_; lean_object* v_ref_1107_; uint8_t v_suppressElabErrors_1108_; uint8_t v_isRecordingDeps_1109_; lean_object* v_fileName_1110_; lean_object* v_fileMap_1111_; lean_object* v_options_1112_; lean_object* v_currNamespace_1113_; lean_object* v_openDecls_1114_; lean_object* v_initHeartbeats_1115_; lean_object* v_maxHeartbeats_1116_; lean_object* v_quotContext_1117_; lean_object* v_currMacroScope_1118_; lean_object* v_cancelTk_x3f_1119_; lean_object* v_inheritedTraceOptions_1120_; uint8_t v___y_1122_; lean_object* v___y_1123_; uint16_t v___y_1124_; uint8_t v___y_1147_; lean_object* v___y_1148_; uint16_t v___y_1149_; uint8_t v___y_1150_; lean_object* v___y_1152_; uint8_t v___y_1153_; uint16_t v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1157_; 
v_toCold_1105_ = lean_ctor_get(v___y_996_, 0);
v_currRecDepth_1106_ = lean_ctor_get(v___y_996_, 1);
v_ref_1107_ = lean_ctor_get(v___y_996_, 2);
v_suppressElabErrors_1108_ = lean_ctor_get_uint8(v___y_996_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1109_ = lean_ctor_get_uint8(v___y_996_, sizeof(void*)*3 + 3);
v_fileName_1110_ = lean_ctor_get(v_toCold_1105_, 0);
v_fileMap_1111_ = lean_ctor_get(v_toCold_1105_, 1);
v_options_1112_ = lean_ctor_get(v_toCold_1105_, 2);
v_currNamespace_1113_ = lean_ctor_get(v_toCold_1105_, 4);
v_openDecls_1114_ = lean_ctor_get(v_toCold_1105_, 5);
v_initHeartbeats_1115_ = lean_ctor_get(v_toCold_1105_, 6);
v_maxHeartbeats_1116_ = lean_ctor_get(v_toCold_1105_, 7);
v_quotContext_1117_ = lean_ctor_get(v_toCold_1105_, 8);
v_currMacroScope_1118_ = lean_ctor_get(v_toCold_1105_, 9);
v_cancelTk_x3f_1119_ = lean_ctor_get(v_toCold_1105_, 10);
v_inheritedTraceOptions_1120_ = lean_ctor_get(v_toCold_1105_, 11);
if (v_isRecordingDeps_1109_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1112_);
v___x_1167_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_options_1112_, v___x_1166_, v_a_992_);
v___y_1157_ = v___x_1167_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1168_; 
lean_inc_ref(v_options_1112_);
v___x_1168_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1112_);
v___y_1157_ = v___x_1168_;
goto v___jp_1156_;
}
v___jp_999_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1003_ = l_Lean_stringToMessageData(v_kind_987_);
v___x_1004_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_inc_ref(v___y_1002_);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___y_1002_);
v___x_1007_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4);
v___x_1010_ = l_Lean_MessageData_joinSep(v___y_1001_, v___x_1009_);
v___x_1011_ = l_Lean_indentD(v___x_1010_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1008_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_Exception_toMessageData(v___y_1000_);
v___x_1016_ = l_Lean_indentD(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1014_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
v___jp_1020_:
{
if (v___y_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v_diag_1026_; lean_object* v_unfoldCounter_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_env_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1025_ = lean_st_ref_get(v___y_995_);
v_diag_1026_ = lean_ctor_get(v___x_1025_, 4);
lean_inc_ref(v_diag_1026_);
lean_dec(v___x_1025_);
v_unfoldCounter_1027_ = lean_ctor_get(v_diag_1026_, 0);
lean_inc_ref(v_unfoldCounter_1027_);
lean_dec_ref(v_diag_1026_);
v___x_1028_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v___y_1022_, v_unfoldCounter_1027_);
lean_dec_ref(v___y_1022_);
v___x_1029_ = lean_st_ref_get(v___y_1023_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_env_1030_);
lean_dec(v___x_1029_);
v___x_1031_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1032_ = lean_mk_empty_array_with_capacity(v___x_988_);
v___x_1033_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_env_1030_, v___x_1031_, v___x_1032_);
v___x_1034_ = l_List_isEmpty___redArg(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7));
v___x_1036_ = lean_string_dec_eq(v_kind_987_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10);
v___y_1000_ = v___y_1021_;
v___y_1001_ = v___x_1033_;
v___y_1002_ = v___x_1037_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13);
v___y_1000_ = v___y_1021_;
v___y_1001_ = v___x_1033_;
v___y_1002_ = v___x_1038_;
goto v___jp_999_;
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v___x_1033_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_kind_987_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
else
{
lean_object* v___x_1041_; 
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_kind_987_);
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___y_1021_);
return v___x_1041_;
}
}
v___jp_1042_:
{
if (v___y_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref(v___y_1043_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___y_1043_);
return v___x_1047_;
}
}
v___jp_1048_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1066_ = l_Lean_maxRecDepth;
v___x_1067_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v___y_1049_, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1068_, 0, v_fileName_1051_);
lean_ctor_set(v___x_1068_, 1, v_fileMap_1052_);
lean_ctor_set(v___x_1068_, 2, v___y_1049_);
lean_ctor_set(v___x_1068_, 3, v___x_1067_);
lean_ctor_set(v___x_1068_, 4, v_currNamespace_1053_);
lean_ctor_set(v___x_1068_, 5, v_openDecls_1054_);
lean_ctor_set(v___x_1068_, 6, v_initHeartbeats_1055_);
lean_ctor_set(v___x_1068_, 7, v_maxHeartbeats_1056_);
lean_ctor_set(v___x_1068_, 8, v_quotContext_1057_);
lean_ctor_set(v___x_1068_, 9, v_currMacroScope_1058_);
lean_ctor_set(v___x_1068_, 10, v_cancelTk_x3f_1059_);
lean_ctor_set(v___x_1068_, 11, v_inheritedTraceOptions_1060_);
lean_inc(v_ref_1062_);
lean_inc(v_currRecDepth_1061_);
v___x_1069_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_currRecDepth_1061_);
lean_ctor_set(v___x_1069_, 2, v_ref_1062_);
lean_ctor_set_uint16(v___x_1069_, sizeof(void*)*3, v___y_1050_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*3 + 2, v_suppressElabErrors_1063_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*3 + 3, v_isRecordingDeps_1064_);
lean_inc_ref(v_a_989_);
v___x_1070_ = l_Lean_Meta_check(v_a_989_, v___x_990_, v___y_994_, v___y_995_, v___x_1069_, v___y_1065_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1071_; lean_object* v_diag_1072_; lean_object* v_unfoldCounter_1073_; lean_object* v___x_1074_; lean_object* v_mctx_1075_; lean_object* v_cache_1076_; lean_object* v_zetaDeltaFVarIds_1077_; lean_object* v_postponed_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref_known(v___x_1070_, 1);
v___x_1071_ = lean_st_ref_get(v___y_995_);
v_diag_1072_ = lean_ctor_get(v___x_1071_, 4);
lean_inc_ref(v_diag_1072_);
lean_dec(v___x_1071_);
v_unfoldCounter_1073_ = lean_ctor_get(v_diag_1072_, 0);
lean_inc_ref(v_unfoldCounter_1073_);
lean_dec_ref(v_diag_1072_);
v___x_1074_ = lean_st_ref_take(v___y_995_);
v_mctx_1075_ = lean_ctor_get(v___x_1074_, 0);
v_cache_1076_ = lean_ctor_get(v___x_1074_, 1);
v_zetaDeltaFVarIds_1077_ = lean_ctor_get(v___x_1074_, 2);
v_postponed_1078_ = lean_ctor_get(v___x_1074_, 3);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1074_, 4);
lean_dec(v_unused_1101_);
v___x_1080_ = v___x_1074_;
v_isShared_1081_ = v_isSharedCheck_1100_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_postponed_1078_);
lean_inc(v_zetaDeltaFVarIds_1077_);
lean_inc(v_cache_1076_);
lean_inc(v_mctx_1075_);
lean_dec(v___x_1074_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1100_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 4, v_diag_991_);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_mctx_1075_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_cache_1076_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_zetaDeltaFVarIds_1077_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_postponed_1078_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_diag_991_);
v___x_1083_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_st_ref_put(v___y_995_, v___x_1083_);
v___x_1085_ = 5;
v___x_1086_ = l_Lean_Meta_check(v_a_989_, v___x_1085_, v___y_994_, v___y_995_, v___x_1069_, v___y_1065_);
lean_dec_ref_known(v___x_1069_, 3);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_unfoldCounter_1073_);
lean_dec_ref(v_kind_987_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1095_);
v___x_1088_ = v___x_1086_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v___x_1086_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1096_; uint8_t v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1097_ = l_Lean_Exception_isInterrupt(v_a_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
lean_inc(v_a_1096_);
v___x_1098_ = l_Lean_Exception_isRuntime(v_a_1096_);
v___y_1021_ = v_a_1096_;
v___y_1022_ = v_unfoldCounter_1073_;
v___y_1023_ = v___y_1065_;
v___y_1024_ = v___x_1098_;
goto v___jp_1020_;
}
else
{
v___y_1021_ = v_a_1096_;
v___y_1022_ = v_unfoldCounter_1073_;
v___y_1023_ = v___y_1065_;
v___y_1024_ = v___x_1097_;
goto v___jp_1020_;
}
}
}
}
}
else
{
lean_object* v_a_1102_; uint8_t v___x_1103_; 
lean_dec_ref_known(v___x_1069_, 3);
lean_dec_ref(v_diag_991_);
lean_dec_ref(v_a_989_);
lean_dec_ref(v_kind_987_);
v_a_1102_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1103_ = l_Lean_Exception_isInterrupt(v_a_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; 
lean_inc(v_a_1102_);
v___x_1104_ = l_Lean_Exception_isRuntime(v_a_1102_);
v___y_1043_ = v_a_1102_;
v___y_1044_ = v___x_1104_;
goto v___jp_1042_;
}
else
{
v___y_1043_ = v_a_1102_;
v___y_1044_ = v___x_1103_;
goto v___jp_1042_;
}
}
}
v___jp_1121_:
{
lean_object* v___x_1125_; lean_object* v_env_1126_; lean_object* v_nextMacroScope_1127_; lean_object* v_ngen_1128_; lean_object* v_auxDeclNGen_1129_; lean_object* v_traceState_1130_; lean_object* v_recordedDeps_1131_; lean_object* v_messages_1132_; lean_object* v_infoState_1133_; lean_object* v_snapshotTasks_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1144_; 
v___x_1125_ = lean_st_ref_take(v___y_997_);
v_env_1126_ = lean_ctor_get(v___x_1125_, 0);
v_nextMacroScope_1127_ = lean_ctor_get(v___x_1125_, 1);
v_ngen_1128_ = lean_ctor_get(v___x_1125_, 2);
v_auxDeclNGen_1129_ = lean_ctor_get(v___x_1125_, 3);
v_traceState_1130_ = lean_ctor_get(v___x_1125_, 4);
v_recordedDeps_1131_ = lean_ctor_get(v___x_1125_, 6);
v_messages_1132_ = lean_ctor_get(v___x_1125_, 7);
v_infoState_1133_ = lean_ctor_get(v___x_1125_, 8);
v_snapshotTasks_1134_ = lean_ctor_get(v___x_1125_, 9);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1125_, 5);
lean_dec(v_unused_1145_);
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snapshotTasks_1134_);
lean_inc(v_infoState_1133_);
lean_inc(v_messages_1132_);
lean_inc(v_recordedDeps_1131_);
lean_inc(v_traceState_1130_);
lean_inc(v_auxDeclNGen_1129_);
lean_inc(v_ngen_1128_);
lean_inc(v_nextMacroScope_1127_);
lean_inc(v_env_1126_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = l_Lean_Kernel_enableDiag(v_env_1126_, v___y_1122_);
v___x_1139_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 5, v___x_1139_);
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_nextMacroScope_1127_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_ngen_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_auxDeclNGen_1129_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_traceState_1130_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1143_, 6, v_recordedDeps_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 7, v_messages_1132_);
lean_ctor_set(v_reuseFailAlloc_1143_, 8, v_infoState_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 9, v_snapshotTasks_1134_);
v___x_1141_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_st_ref_put(v___y_997_, v___x_1141_);
lean_inc_ref(v_inheritedTraceOptions_1120_);
lean_inc(v_cancelTk_x3f_1119_);
lean_inc(v_currMacroScope_1118_);
lean_inc(v_quotContext_1117_);
lean_inc(v_maxHeartbeats_1116_);
lean_inc(v_initHeartbeats_1115_);
lean_inc(v_openDecls_1114_);
lean_inc(v_currNamespace_1113_);
lean_inc_ref(v_fileMap_1111_);
lean_inc_ref(v_fileName_1110_);
v___y_1049_ = v___y_1123_;
v___y_1050_ = v___y_1124_;
v_fileName_1051_ = v_fileName_1110_;
v_fileMap_1052_ = v_fileMap_1111_;
v_currNamespace_1053_ = v_currNamespace_1113_;
v_openDecls_1054_ = v_openDecls_1114_;
v_initHeartbeats_1055_ = v_initHeartbeats_1115_;
v_maxHeartbeats_1056_ = v_maxHeartbeats_1116_;
v_quotContext_1057_ = v_quotContext_1117_;
v_currMacroScope_1058_ = v_currMacroScope_1118_;
v_cancelTk_x3f_1059_ = v_cancelTk_x3f_1119_;
v_inheritedTraceOptions_1060_ = v_inheritedTraceOptions_1120_;
v_currRecDepth_1061_ = v_currRecDepth_1106_;
v_ref_1062_ = v_ref_1107_;
v_suppressElabErrors_1063_ = v_suppressElabErrors_1108_;
v_isRecordingDeps_1064_ = v_isRecordingDeps_1109_;
v___y_1065_ = v___y_997_;
goto v___jp_1048_;
}
}
}
v___jp_1146_:
{
if (v___y_1150_ == 0)
{
v___y_1122_ = v___y_1147_;
v___y_1123_ = v___y_1148_;
v___y_1124_ = v___y_1149_;
goto v___jp_1121_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1120_);
lean_inc(v_cancelTk_x3f_1119_);
lean_inc(v_currMacroScope_1118_);
lean_inc(v_quotContext_1117_);
lean_inc(v_maxHeartbeats_1116_);
lean_inc(v_initHeartbeats_1115_);
lean_inc(v_openDecls_1114_);
lean_inc(v_currNamespace_1113_);
lean_inc_ref(v_fileMap_1111_);
lean_inc_ref(v_fileName_1110_);
v___y_1049_ = v___y_1148_;
v___y_1050_ = v___y_1149_;
v_fileName_1051_ = v_fileName_1110_;
v_fileMap_1052_ = v_fileMap_1111_;
v_currNamespace_1053_ = v_currNamespace_1113_;
v_openDecls_1054_ = v_openDecls_1114_;
v_initHeartbeats_1055_ = v_initHeartbeats_1115_;
v_maxHeartbeats_1056_ = v_maxHeartbeats_1116_;
v_quotContext_1057_ = v_quotContext_1117_;
v_currMacroScope_1058_ = v_currMacroScope_1118_;
v_cancelTk_x3f_1059_ = v_cancelTk_x3f_1119_;
v_inheritedTraceOptions_1060_ = v_inheritedTraceOptions_1120_;
v_currRecDepth_1061_ = v_currRecDepth_1106_;
v_ref_1062_ = v_ref_1107_;
v_suppressElabErrors_1063_ = v_suppressElabErrors_1108_;
v_isRecordingDeps_1064_ = v_isRecordingDeps_1109_;
v___y_1065_ = v___y_997_;
goto v___jp_1048_;
}
}
v___jp_1151_:
{
if (v___y_1155_ == 0)
{
if (v___y_1153_ == 0)
{
v___y_1147_ = v___y_1155_;
v___y_1148_ = v___y_1152_;
v___y_1149_ = v___y_1154_;
v___y_1150_ = v_a_992_;
goto v___jp_1146_;
}
else
{
v___y_1122_ = v___y_1155_;
v___y_1123_ = v___y_1152_;
v___y_1124_ = v___y_1154_;
goto v___jp_1121_;
}
}
else
{
v___y_1147_ = v___y_1155_;
v___y_1148_ = v___y_1152_;
v___y_1149_ = v___y_1154_;
v___y_1150_ = v___y_1153_;
goto v___jp_1146_;
}
}
v___jp_1156_:
{
uint16_t v___x_1158_; lean_object* v___x_1159_; lean_object* v_env_1160_; uint8_t v___x_1161_; uint16_t v___x_1162_; uint16_t v___x_1163_; uint16_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1158_ = l_Lean_OptionFlags_ofOptions(v___y_1157_);
v___x_1159_ = lean_st_ref_get(v___y_997_);
v_env_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_env_1160_);
lean_dec(v___x_1159_);
v___x_1161_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1160_);
lean_dec_ref(v_env_1160_);
v___x_1162_ = 512;
v___x_1163_ = lean_uint16_land(v___x_1158_, v___x_1162_);
v___x_1164_ = 0;
v___x_1165_ = lean_uint16_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
v___y_1152_ = v___y_1157_;
v___y_1153_ = v___x_1161_;
v___y_1154_ = v___x_1158_;
v___y_1155_ = v_a_992_;
goto v___jp_1151_;
}
else
{
v___y_1152_ = v___y_1157_;
v___y_1153_ = v___x_1161_;
v___y_1154_ = v___x_1158_;
v___y_1155_ = v_val_993_;
goto v___jp_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed(lean_object* v_kind_1169_, lean_object* v___x_1170_, lean_object* v_a_1171_, lean_object* v___x_1172_, lean_object* v_diag_1173_, lean_object* v_a_1174_, lean_object* v_val_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v___x_27062__boxed_1181_; uint8_t v_a_27063__boxed_1182_; uint8_t v_val_27064__boxed_1183_; lean_object* v_res_1184_; 
v___x_27062__boxed_1181_ = lean_unbox(v___x_1172_);
v_a_27063__boxed_1182_ = lean_unbox(v_a_1174_);
v_val_27064__boxed_1183_ = lean_unbox(v_val_1175_);
v_res_1184_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(v_kind_1169_, v___x_1170_, v_a_1171_, v___x_27062__boxed_1181_, v_diag_1173_, v_a_27063__boxed_1182_, v_val_27064__boxed_1183_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___x_1170_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object* v_kind_1190_, uint8_t v_a_1191_, uint8_t v_val_1192_, lean_object* v_as_x27_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
if (lean_obj_tag(v_as_x27_1193_) == 0)
{
lean_object* v___x_1200_; 
lean_dec_ref(v_kind_1190_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_b_1194_);
return v___x_1200_;
}
else
{
lean_object* v_head_1201_; lean_object* v_tail_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_a_1206_; lean_object* v___x_1211_; lean_object* v_mctx_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_b_1194_);
v_head_1201_ = lean_ctor_get(v_as_x27_1193_, 0);
v_tail_1202_ = lean_ctor_get(v_as_x27_1193_, 1);
v___x_1203_ = lean_box(0);
v___x_1204_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0));
v___x_1211_ = lean_st_ref_get(v___y_1196_);
v_mctx_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_mctx_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1212_, v_head_1201_);
lean_dec_ref(v_mctx_1212_);
if (lean_obj_tag(v___x_1213_) == 1)
{
lean_object* v_val_1214_; lean_object* v_lctx_1215_; lean_object* v_type_1216_; lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v_diag_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v_val_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_lctx_1215_ = lean_ctor_get(v_val_1214_, 1);
lean_inc_ref(v_lctx_1215_);
v_type_1216_ = lean_ctor_get(v_val_1214_, 2);
lean_inc_ref(v_type_1216_);
lean_dec(v_val_1214_);
v___x_1217_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_1216_, v___y_1196_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = lean_st_ref_get(v___y_1196_);
v_diag_1220_ = lean_ctor_get(v___x_1219_, 4);
lean_inc_ref_n(v_diag_1220_, 2);
lean_dec(v___x_1219_);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__1));
v___x_1223_ = 1;
v___x_1224_ = lean_box(v___x_1223_);
v___x_1225_ = lean_box(v_a_1191_);
v___x_1226_ = lean_box(v_val_1192_);
lean_inc_ref(v_kind_1190_);
v___f_1227_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1227_, 0, v_kind_1190_);
lean_closure_set(v___f_1227_, 1, v___x_1221_);
lean_closure_set(v___f_1227_, 2, v_a_1218_);
lean_closure_set(v___f_1227_, 3, v___x_1224_);
lean_closure_set(v___f_1227_, 4, v_diag_1220_);
lean_closure_set(v___f_1227_, 5, v___x_1225_);
lean_closure_set(v___f_1227_, 6, v___x_1226_);
v___x_1228_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(v_lctx_1215_, v___x_1222_, v___f_1227_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v_mctx_1231_; lean_object* v_cache_1232_; lean_object* v_zetaDeltaFVarIds_1233_; lean_object* v_postponed_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1242_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = lean_st_ref_take(v___y_1196_);
v_mctx_1231_ = lean_ctor_get(v___x_1230_, 0);
v_cache_1232_ = lean_ctor_get(v___x_1230_, 1);
v_zetaDeltaFVarIds_1233_ = lean_ctor_get(v___x_1230_, 2);
v_postponed_1234_ = lean_ctor_get(v___x_1230_, 3);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1230_, 4);
lean_dec(v_unused_1243_);
v___x_1236_ = v___x_1230_;
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_postponed_1234_);
lean_inc(v_zetaDeltaFVarIds_1233_);
lean_inc(v_cache_1232_);
lean_inc(v_mctx_1231_);
lean_dec(v___x_1230_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 4, v_diag_1220_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_mctx_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_cache_1232_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_zetaDeltaFVarIds_1233_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_postponed_1234_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_diag_1220_);
v___x_1239_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_st_ref_put(v___y_1196_, v___x_1239_);
v_a_1206_ = v_a_1229_;
goto v___jp_1205_;
}
}
}
else
{
lean_dec_ref(v_diag_1220_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1244_; 
v_a_1244_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1228_, 1);
v_a_1206_ = v_a_1244_;
goto v___jp_1205_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_kind_1190_);
v_a_1245_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1228_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1228_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_dec(v___x_1213_);
v_as_x27_1193_ = v_tail_1202_;
v_b_1194_ = v___x_1204_;
goto _start;
}
v___jp_1205_:
{
if (lean_obj_tag(v_a_1206_) == 1)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_kind_1190_);
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_a_1206_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1203_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
else
{
lean_dec(v_a_1206_);
v_as_x27_1193_ = v_tail_1202_;
v_b_1194_ = v___x_1204_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object* v_kind_1254_, lean_object* v_a_1255_, lean_object* v_val_1256_, lean_object* v_as_x27_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_a_27370__boxed_1264_; uint8_t v_val_27371__boxed_1265_; lean_object* v_res_1266_; 
v_a_27370__boxed_1264_ = lean_unbox(v_a_1255_);
v_val_27371__boxed_1265_ = lean_unbox(v_val_1256_);
v_res_1266_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1254_, v_a_27370__boxed_1264_, v_val_27371__boxed_1265_, v_as_x27_1257_, v_b_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_as_x27_1257_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(uint8_t v_a_1267_, uint8_t v_val_1268_, lean_object* v_kind_1269_, lean_object* v_goals_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0));
v___x_1278_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1269_, v_a_1267_, v_val_1268_, v_goals_1270_, v___x_1277_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1291_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_fst_1283_; 
v_fst_1283_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_fst_1283_);
lean_dec(v_a_1279_);
if (lean_obj_tag(v_fst_1283_) == 0)
{
lean_object* v___x_1285_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1276_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1276_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1289_; 
v_val_1287_ = lean_ctor_get(v_fst_1283_, 0);
lean_inc(v_val_1287_);
lean_dec_ref_known(v_fst_1283_, 1);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_val_1287_);
v___x_1289_ = v___x_1281_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_val_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1278_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1278_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed(lean_object* v_a_1300_, lean_object* v_val_1301_, lean_object* v_kind_1302_, lean_object* v_goals_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v_a_27493__boxed_1309_; uint8_t v_val_27494__boxed_1310_; lean_object* v_res_1311_; 
v_a_27493__boxed_1309_ = lean_unbox(v_a_1300_);
v_val_27494__boxed_1310_ = lean_unbox(v_val_1301_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(v_a_27493__boxed_1309_, v_val_27494__boxed_1310_, v_kind_1302_, v_goals_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v_goals_1303_);
return v_res_1311_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = lean_box(1);
v___x_1315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_1316_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0);
v___x_1317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_ctor_set(v___x_1317_, 2, v___x_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(lean_object* v_val_1319_, uint8_t v_a_1320_, lean_object* v___x_1321_, lean_object* v_ci_1322_, lean_object* v_info_1323_, lean_object* v_x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_st_ref_get(v_val_1319_);
v___x_1329_ = lean_unbox(v___x_1328_);
if (v___x_1329_ == 0)
{
if (lean_obj_tag(v_info_1323_) == 0)
{
lean_object* v_toCommandContextInfo_1330_; lean_object* v_i_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1408_; 
v_toCommandContextInfo_1330_ = lean_ctor_get(v_ci_1322_, 0);
lean_inc_ref(v_toCommandContextInfo_1330_);
v_i_1331_ = lean_ctor_get(v_info_1323_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_info_1323_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1333_ = v_info_1323_;
v_isShared_1334_ = v_isSharedCheck_1408_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_i_1331_);
lean_dec(v_info_1323_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1408_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_parentDecl_x3f_1335_; lean_object* v_autoImplicits_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1406_; 
v_parentDecl_x3f_1335_ = lean_ctor_get(v_ci_1322_, 1);
v_autoImplicits_1336_ = lean_ctor_get(v_ci_1322_, 2);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_ci_1322_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_ci_1322_, 0);
lean_dec(v_unused_1407_);
v___x_1338_ = v_ci_1322_;
v_isShared_1339_ = v_isSharedCheck_1406_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_autoImplicits_1336_);
lean_inc(v_parentDecl_x3f_1335_);
lean_dec(v_ci_1322_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1406_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_env_1340_; lean_object* v_cmdEnv_x3f_1341_; lean_object* v_fileMap_1342_; lean_object* v_options_1343_; lean_object* v_currNamespace_1344_; lean_object* v_openDecls_1345_; lean_object* v_ngen_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1404_; 
v_env_1340_ = lean_ctor_get(v_toCommandContextInfo_1330_, 0);
v_cmdEnv_x3f_1341_ = lean_ctor_get(v_toCommandContextInfo_1330_, 1);
v_fileMap_1342_ = lean_ctor_get(v_toCommandContextInfo_1330_, 2);
v_options_1343_ = lean_ctor_get(v_toCommandContextInfo_1330_, 4);
v_currNamespace_1344_ = lean_ctor_get(v_toCommandContextInfo_1330_, 5);
v_openDecls_1345_ = lean_ctor_get(v_toCommandContextInfo_1330_, 6);
v_ngen_1346_ = lean_ctor_get(v_toCommandContextInfo_1330_, 7);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_toCommandContextInfo_1330_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_toCommandContextInfo_1330_, 3);
lean_dec(v_unused_1405_);
v___x_1348_ = v_toCommandContextInfo_1330_;
v_isShared_1349_ = v_isSharedCheck_1404_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_ngen_1346_);
lean_inc(v_openDecls_1345_);
lean_inc(v_currNamespace_1344_);
lean_inc(v_options_1343_);
lean_inc(v_fileMap_1342_);
lean_inc(v_cmdEnv_x3f_1341_);
lean_inc(v_env_1340_);
lean_dec(v_toCommandContextInfo_1330_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1404_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_toElabInfo_1350_; lean_object* v_mctxBefore_1351_; lean_object* v_goalsBefore_1352_; lean_object* v_mctxAfter_1353_; lean_object* v_goalsAfter_1354_; lean_object* v___y_1356_; lean_object* v___x_1387_; 
v_toElabInfo_1350_ = lean_ctor_get(v_i_1331_, 0);
lean_inc_ref(v_toElabInfo_1350_);
v_mctxBefore_1351_ = lean_ctor_get(v_i_1331_, 1);
lean_inc_ref(v_mctxBefore_1351_);
v_goalsBefore_1352_ = lean_ctor_get(v_i_1331_, 2);
lean_inc(v_goalsBefore_1352_);
v_mctxAfter_1353_ = lean_ctor_get(v_i_1331_, 3);
lean_inc_ref(v_mctxAfter_1353_);
v_goalsAfter_1354_ = lean_ctor_get(v_i_1331_, 4);
lean_inc(v_goalsAfter_1354_);
lean_dec_ref(v_i_1331_);
lean_inc_ref(v_ngen_1346_);
lean_inc(v_openDecls_1345_);
lean_inc(v_currNamespace_1344_);
lean_inc_ref(v_options_1343_);
lean_inc_ref(v_fileMap_1342_);
lean_inc(v_cmdEnv_x3f_1341_);
lean_inc_ref(v_env_1340_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 3, v_mctxBefore_1351_);
v___x_1387_ = v___x_1348_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_env_1340_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_cmdEnv_x3f_1341_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_fileMap_1342_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_mctxBefore_1351_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_options_1343_);
lean_ctor_set(v_reuseFailAlloc_1403_, 5, v_currNamespace_1344_);
lean_ctor_set(v_reuseFailAlloc_1403_, 6, v_openDecls_1345_);
lean_ctor_set(v_reuseFailAlloc_1403_, 7, v_ngen_1346_);
v___x_1387_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1386_;
}
v___jp_1355_:
{
if (lean_obj_tag(v___y_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1333_);
v_a_1357_ = lean_ctor_get(v___y_1356_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___y_1356_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1359_ = v___y_1356_;
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___y_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
if (lean_obj_tag(v_a_1357_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_stx_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1359_);
v_val_1361_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v_a_1357_, 1);
v___x_1362_ = lean_box(v_a_1320_);
v___x_1363_ = lean_st_ref_swap(v_val_1319_, v___x_1362_);
lean_dec(v___x_1363_);
v_stx_1364_ = lean_ctor_get(v_toElabInfo_1350_, 1);
lean_inc(v_stx_1364_);
lean_dec_ref(v_toElabInfo_1350_);
v___x_1365_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v___x_1321_, v_stx_1364_, v_val_1361_, v___y_1325_, v___y_1326_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec(v_a_1357_);
lean_dec_ref(v_toElabInfo_1350_);
lean_dec_ref(v___x_1321_);
v___x_1366_ = lean_box(0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1366_);
v___x_1368_ = v___x_1359_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v_toElabInfo_1350_);
lean_dec_ref(v___x_1321_);
v_a_1371_ = lean_ctor_get(v___y_1356_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___y_1356_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1373_ = v___y_1356_;
v_isShared_1374_ = v_isSharedCheck_1385_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___y_1356_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1385_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_ref_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v_ref_1375_ = lean_ctor_get(v___y_1325_, 7);
v___x_1376_ = lean_io_error_to_string(v_a_1371_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 3);
lean_ctor_set(v___x_1333_, 0, v___x_1376_);
v___x_1378_ = v___x_1333_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = l_Lean_MessageData_ofFormat(v___x_1378_);
lean_inc(v_ref_1375_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_ref_1375_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1380_);
v___x_1382_ = v___x_1373_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
lean_inc_ref(v_autoImplicits_1336_);
lean_inc(v_parentDecl_x3f_1335_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1387_);
v___x_1389_ = v___x_1338_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_parentDecl_x3f_1335_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_autoImplicits_1336_);
v___x_1389_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1390_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1390_, 0, v_env_1340_);
lean_ctor_set(v___x_1390_, 1, v_cmdEnv_x3f_1341_);
lean_ctor_set(v___x_1390_, 2, v_fileMap_1342_);
lean_ctor_set(v___x_1390_, 3, v_mctxAfter_1353_);
lean_ctor_set(v___x_1390_, 4, v_options_1343_);
lean_ctor_set(v___x_1390_, 5, v_currNamespace_1344_);
lean_ctor_set(v___x_1390_, 6, v_openDecls_1345_);
lean_ctor_set(v___x_1390_, 7, v_ngen_1346_);
v___x_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_parentDecl_x3f_1335_);
lean_ctor_set(v___x_1391_, 2, v_autoImplicits_1336_);
v___x_1392_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1);
v___x_1393_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7));
v___x_1394_ = lean_box(v_a_1320_);
lean_inc(v___x_1328_);
v___x_1395_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed), 9, 4);
lean_closure_set(v___x_1395_, 0, v___x_1394_);
lean_closure_set(v___x_1395_, 1, v___x_1328_);
lean_closure_set(v___x_1395_, 2, v___x_1393_);
lean_closure_set(v___x_1395_, 3, v_goalsBefore_1352_);
v___x_1396_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_1389_, v___x_1392_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
if (lean_obj_tag(v_a_1397_) == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__2));
v___x_1399_ = lean_box(v_a_1320_);
v___x_1400_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed), 9, 4);
lean_closure_set(v___x_1400_, 0, v___x_1399_);
lean_closure_set(v___x_1400_, 1, v___x_1328_);
lean_closure_set(v___x_1400_, 2, v___x_1398_);
lean_closure_set(v___x_1400_, 3, v_goalsAfter_1354_);
v___x_1401_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_1391_, v___x_1392_, v___x_1400_);
v___y_1356_ = v___x_1401_;
goto v___jp_1355_;
}
else
{
lean_dec_ref_known(v___x_1391_, 3);
lean_dec(v_goalsAfter_1354_);
lean_dec(v___x_1328_);
v___y_1356_ = v___x_1396_;
goto v___jp_1355_;
}
}
else
{
lean_dec_ref_known(v___x_1391_, 3);
lean_dec(v_goalsAfter_1354_);
lean_dec(v___x_1328_);
v___y_1356_ = v___x_1396_;
goto v___jp_1355_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec(v___x_1328_);
lean_dec_ref(v_info_1323_);
lean_dec_ref(v_ci_1322_);
lean_dec_ref(v___x_1321_);
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
return v___x_1410_;
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec(v___x_1328_);
lean_dec_ref(v_info_1323_);
lean_dec_ref(v_ci_1322_);
lean_dec_ref(v___x_1321_);
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed(lean_object* v_val_1413_, lean_object* v_a_1414_, lean_object* v___x_1415_, lean_object* v_ci_1416_, lean_object* v_info_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v_a_27588__boxed_1422_; lean_object* v_res_1423_; 
v_a_27588__boxed_1422_ = lean_unbox(v_a_1414_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(v_val_1413_, v_a_27588__boxed_1422_, v___x_1415_, v_ci_1416_, v_info_1417_, v_x_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v_x_1418_);
lean_dec(v_val_1413_);
return v_res_1423_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_instMonadEIO___redArg();
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_toApplicative_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1464_; 
v___x_1431_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0);
v___x_1432_ = l_StateRefT_x27_instMonad___redArg(v___x_1431_);
v_toApplicative_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1432_, 1);
lean_dec(v_unused_1465_);
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1464_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_toApplicative_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1464_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_toFunctor_1437_; lean_object* v_toSeq_1438_; lean_object* v_toSeqLeft_1439_; lean_object* v_toSeqRight_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1462_; 
v_toFunctor_1437_ = lean_ctor_get(v_toApplicative_1433_, 0);
v_toSeq_1438_ = lean_ctor_get(v_toApplicative_1433_, 2);
v_toSeqLeft_1439_ = lean_ctor_get(v_toApplicative_1433_, 3);
v_toSeqRight_1440_ = lean_ctor_get(v_toApplicative_1433_, 4);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_toApplicative_1433_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_toApplicative_1433_, 1);
lean_dec(v_unused_1463_);
v___x_1442_ = v_toApplicative_1433_;
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_toSeqRight_1440_);
lean_inc(v_toSeqLeft_1439_);
lean_inc(v_toSeq_1438_);
lean_inc(v_toFunctor_1437_);
lean_dec(v_toApplicative_1433_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1462_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___x_1453_; 
v___f_1444_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__1));
v___f_1445_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__2));
lean_inc_ref(v_toFunctor_1437_);
v___f_1446_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1446_, 0, v_toFunctor_1437_);
v___f_1447_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1447_, 0, v_toFunctor_1437_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___f_1446_);
lean_ctor_set(v___x_1448_, 1, v___f_1447_);
v___f_1449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1449_, 0, v_toSeqRight_1440_);
v___f_1450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1450_, 0, v_toSeqLeft_1439_);
v___f_1451_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1451_, 0, v_toSeq_1438_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v___f_1449_);
lean_ctor_set(v___x_1442_, 3, v___f_1450_);
lean_ctor_set(v___x_1442_, 2, v___f_1451_);
lean_ctor_set(v___x_1442_, 1, v___f_1444_);
lean_ctor_set(v___x_1442_, 0, v___x_1448_);
v___x_1453_ = v___x_1442_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___f_1444_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v___f_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v___f_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v___f_1449_);
v___x_1453_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___f_1445_);
lean_ctor_set(v___x_1435_, 0, v___x_1453_);
v___x_1455_ = v___x_1435_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___f_1445_);
v___x_1455_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_22909__overap_1458_; lean_object* v___x_1459_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = l_instInhabitedOfMonad___redArg(v___x_1455_, v___x_1456_);
v___x_22909__overap_1458_ = lean_panic_fn_borrowed(v___x_1457_, v_msg_1427_);
lean_dec(v___x_1457_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
v___x_1459_ = lean_apply_3(v___x_22909__overap_1458_, v___y_1428_, v___y_1429_, lean_box(0));
return v___x_1459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_msg_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v_msg_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1470_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1474_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__2));
v___x_1475_ = lean_unsigned_to_nat(21u);
v___x_1476_ = lean_unsigned_to_nat(65u);
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__1));
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__0));
v___x_1479_ = l_mkPanicMessageWithDecl(v___x_1478_, v___x_1477_, v___x_1476_, v___x_1475_, v___x_1474_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(lean_object* v_preNode_1480_, lean_object* v_postNode_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
switch(lean_obj_tag(v_x_1483_))
{
case 0:
{
lean_object* v_i_1487_; lean_object* v_t_1488_; lean_object* v___x_1489_; 
v_i_1487_ = lean_ctor_get(v_x_1483_, 0);
lean_inc_ref(v_i_1487_);
v_t_1488_ = lean_ctor_get(v_x_1483_, 1);
lean_inc_ref(v_t_1488_);
lean_dec_ref_known(v_x_1483_, 2);
v___x_1489_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1487_, v_x_1482_);
v_x_1482_ = v___x_1489_;
v_x_1483_ = v_t_1488_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec_ref_known(v_x_1483_, 2);
lean_dec_ref(v_postNode_1481_);
lean_dec_ref(v_preNode_1480_);
v___x_1491_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3);
v___x_1492_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v___x_1491_, v___y_1484_, v___y_1485_);
return v___x_1492_;
}
else
{
lean_object* v_i_1493_; lean_object* v_children_1494_; lean_object* v_val_1495_; lean_object* v___x_1496_; 
v_i_1493_ = lean_ctor_get(v_x_1483_, 0);
lean_inc_ref_n(v_i_1493_, 2);
v_children_1494_ = lean_ctor_get(v_x_1483_, 1);
lean_inc_ref_n(v_children_1494_, 2);
lean_dec_ref_known(v_x_1483_, 2);
v_val_1495_ = lean_ctor_get(v_x_1482_, 0);
lean_inc_n(v_val_1495_, 2);
lean_inc_ref(v_preNode_1480_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
v___x_1496_ = lean_apply_6(v_preNode_1480_, v_val_1495_, v_i_1493_, v_children_1494_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; uint8_t v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_unbox(v_a_1497_);
lean_dec(v_a_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v_preNode_1480_);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1482_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_x_1482_, 0);
lean_dec(v_unused_1524_);
v___x_1500_ = v_x_1482_;
v_isShared_1501_ = v_isSharedCheck_1523_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v_x_1482_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1523_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_box(0);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
v___x_1503_ = lean_apply_7(v_postNode_1481_, v_val_1495_, v_i_1493_, v_children_1494_, v___x_1502_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v_a_1504_);
v___x_1509_ = v___x_1500_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_del_object(v___x_1500_);
v_a_1515_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1503_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1503_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1482_, v_i_1493_);
v___x_1526_ = l_Lean_PersistentArray_toList___redArg(v_children_1494_);
v___x_1527_ = lean_box(0);
lean_inc_ref(v_postNode_1481_);
v___x_1528_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1480_, v_postNode_1481_, v___x_1525_, v___x_1526_, v___x_1527_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
v___x_1530_ = lean_apply_7(v_postNode_1481_, v_val_1495_, v_i_1493_, v_children_1494_, v_a_1529_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1540_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1530_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1530_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_val_1495_);
lean_dec_ref(v_children_1494_);
lean_dec_ref(v_i_1493_);
lean_dec_ref(v_postNode_1481_);
v_a_1548_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1528_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1528_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_val_1495_);
lean_dec_ref(v_children_1494_);
lean_dec_ref(v_i_1493_);
lean_dec_ref_known(v_x_1482_, 1);
lean_dec_ref(v_postNode_1481_);
lean_dec_ref(v_preNode_1480_);
v_a_1556_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1496_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1496_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
default: 
{
lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_x_1482_);
lean_dec_ref(v_postNode_1481_);
lean_dec_ref(v_preNode_1480_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1483_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_x_1483_, 0);
lean_dec(v_unused_1572_);
v___x_1565_ = v_x_1483_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v_x_1483_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_box(0);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(lean_object* v_preNode_1573_, lean_object* v_postNode_1574_, lean_object* v___x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
if (lean_obj_tag(v_x_1576_) == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v___x_1575_);
lean_dec_ref(v_postNode_1574_);
lean_dec_ref(v_preNode_1573_);
v___x_1581_ = l_List_reverse___redArg(v_x_1577_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
else
{
lean_object* v_head_1583_; lean_object* v_tail_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1602_; 
v_head_1583_ = lean_ctor_get(v_x_1576_, 0);
v_tail_1584_ = lean_ctor_get(v_x_1576_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1586_ = v_x_1576_;
v_isShared_1587_ = v_isSharedCheck_1602_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_tail_1584_);
lean_inc(v_head_1583_);
lean_dec(v_x_1576_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1602_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; 
lean_inc(v___x_1575_);
lean_inc_ref(v_postNode_1574_);
lean_inc_ref(v_preNode_1573_);
v___x_1588_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1573_, v_postNode_1574_, v___x_1575_, v_head_1583_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v_x_1577_);
lean_ctor_set(v___x_1586_, 0, v_a_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_x_1577_);
v___x_1591_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
v_x_1576_ = v_tail_1584_;
v_x_1577_ = v___x_1591_;
goto _start;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_del_object(v___x_1586_);
lean_dec(v_tail_1584_);
lean_dec(v_x_1577_);
lean_dec(v___x_1575_);
lean_dec_ref(v_postNode_1574_);
lean_dec_ref(v_preNode_1573_);
v_a_1594_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1588_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1588_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg___boxed(lean_object* v_preNode_1603_, lean_object* v_postNode_1604_, lean_object* v___x_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1603_, v_postNode_1604_, v___x_1605_, v_x_1606_, v_x_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___boxed(lean_object* v_preNode_1612_, lean_object* v_postNode_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1612_, v_postNode_1613_, v_x_1614_, v_x_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(lean_object* v_postNode_1620_, lean_object* v_ci_1621_, lean_object* v_i_1622_, lean_object* v_cs_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
v___x_1628_ = lean_apply_6(v_postNode_1620_, v_ci_1621_, v_i_1622_, v_cs_1623_, v___y_1625_, v___y_1626_, lean_box(0));
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed(lean_object* v_postNode_1629_, lean_object* v_ci_1630_, lean_object* v_i_1631_, lean_object* v_cs_1632_, lean_object* v_x_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(v_postNode_1629_, v_ci_1630_, v_i_1631_, v_cs_1632_, v_x_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_x_1633_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object* v_preNode_1638_, lean_object* v_postNode_1639_, lean_object* v_ctx_x3f_1640_, lean_object* v_t_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1645_, 0, v_postNode_1639_);
v___x_1646_ = lean_box(0);
v___x_1647_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1638_, v___f_1645_, v_ctx_x3f_1640_, v_t_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v___x_1647_, 0);
lean_dec(v_unused_1655_);
v___x_1649_ = v___x_1647_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v___x_1647_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1646_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1647_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1647_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object* v_preNode_1664_, lean_object* v_postNode_1665_, lean_object* v_ctx_x3f_1666_, lean_object* v_t_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_preNode_1664_, v_postNode_1665_, v_ctx_x3f_1666_, v_t_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(uint8_t v_a_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_box(v_a_1672_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object* v_a_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v_a_28168__boxed_1688_; lean_object* v_res_1689_; 
v_a_28168__boxed_1688_ = lean_unbox(v_a_1681_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_a_28168__boxed_1688_, v_x_1682_, v_x_1683_, v_x_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v_x_1684_);
lean_dec_ref(v_x_1683_);
lean_dec_ref(v_x_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(uint8_t v_a_1690_, lean_object* v_val_1691_, lean_object* v_as_1692_, size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1694_, v_sz_1693_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec(v_val_1691_);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_b_1695_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1701_ = lean_box(v_a_1690_);
v___f_1702_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1702_, 0, v___x_1701_);
v___x_1703_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1704_ = lean_box(v_a_1690_);
lean_inc(v_val_1691_);
v___f_1705_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1705_, 0, v_val_1691_);
lean_closure_set(v___f_1705_, 1, v___x_1704_);
lean_closure_set(v___f_1705_, 2, v___x_1703_);
v___x_1706_ = lean_box(0);
v_a_1707_ = lean_array_uget_borrowed(v_as_1692_, v_i_1694_);
v___x_1708_ = lean_box(0);
lean_inc(v_a_1707_);
v___x_1709_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___f_1702_, v___f_1705_, v___x_1708_, v_a_1707_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1709_) == 0)
{
size_t v___x_1710_; size_t v___x_1711_; 
lean_dec_ref_known(v___x_1709_, 1);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1694_, v___x_1710_);
v_i_1694_ = v___x_1711_;
v_b_1695_ = v___x_1706_;
goto _start;
}
else
{
lean_dec(v_val_1691_);
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object* v_a_1713_, lean_object* v_val_1714_, lean_object* v_as_1715_, lean_object* v_sz_1716_, lean_object* v_i_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_a_28193__boxed_1722_; size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_a_28193__boxed_1722_ = lean_unbox(v_a_1713_);
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1716_);
lean_dec(v_sz_1716_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_a_28193__boxed_1722_, v_val_1714_, v_as_1715_, v_sz_boxed_1723_, v_i_boxed_1724_, v_b_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_as_1715_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object* v_opt_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v_scopes_1731_; lean_object* v___x_1732_; lean_object* v_opts_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1729_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1730_ = lean_st_ref_get(v___y_1727_);
v_scopes_1731_ = lean_ctor_get(v___x_1730_, 2);
lean_inc(v_scopes_1731_);
lean_dec(v___x_1730_);
v___x_1732_ = l_List_head_x21___redArg(v___x_1729_, v_scopes_1731_);
lean_dec(v_scopes_1731_);
v_opts_1733_ = lean_ctor_get(v___x_1732_, 1);
lean_inc_ref(v_opts_1733_);
lean_dec(v___x_1732_);
v___x_1734_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_1733_, v_opt_1726_);
lean_dec_ref(v_opts_1733_);
v___x_1735_ = lean_box(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object* v_opt_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v_opt_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object* v___cmdStx_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1776_; 
v___x_1745_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1746_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_1745_, v___y_1743_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1776_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1776_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_unbox(v_a_1747_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_dec(v_a_1747_);
v___x_1752_ = lean_box(0);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1752_);
v___x_1754_ = v___x_1749_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v_infoState_1757_; lean_object* v_trees_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; size_t v_sz_1764_; size_t v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1749_);
v___x_1756_ = lean_st_ref_get(v___y_1743_);
v_infoState_1757_ = lean_ctor_get(v___x_1756_, 8);
lean_inc_ref(v_infoState_1757_);
lean_dec(v___x_1756_);
v_trees_1758_ = lean_ctor_get(v_infoState_1757_, 2);
lean_inc_ref(v_trees_1758_);
lean_dec_ref(v_infoState_1757_);
v___x_1759_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1758_);
lean_dec_ref(v_trees_1758_);
v___x_1760_ = 0;
v___x_1761_ = lean_box(v___x_1760_);
v___x_1762_ = lean_st_mk_ref(v___x_1761_);
v___x_1763_ = lean_box(0);
v_sz_1764_ = lean_array_size(v___x_1759_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = lean_unbox(v_a_1747_);
lean_dec(v_a_1747_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___x_1766_, v___x_1762_, v___x_1759_, v_sz_1764_, v___x_1765_, v___x_1763_, v___y_1742_, v___y_1743_);
lean_dec_ref(v___x_1759_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v___x_1767_, 0);
lean_dec(v_unused_1775_);
v___x_1769_ = v___x_1767_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v___x_1767_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1763_);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1763_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
else
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object* v___cmdStx_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(v___cmdStx_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___cmdStx_1777_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object* v_opt_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1790_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object* v_opt_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_opt_1795_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object* v_00_u03b2_1800_, lean_object* v_m_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v_m_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object* v_00_u03b2_1803_, lean_object* v_m_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_00_u03b2_1803_, v_m_1804_);
lean_dec_ref(v_m_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object* v_kind_1806_, uint8_t v_a_1807_, uint8_t v_val_1808_, lean_object* v_as_1809_, lean_object* v_as_x27_1810_, lean_object* v_b_1811_, lean_object* v_a_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1806_, v_a_1807_, v_val_1808_, v_as_x27_1810_, v_b_1811_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object* v_kind_1819_, lean_object* v_a_1820_, lean_object* v_val_1821_, lean_object* v_as_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v_a_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
uint8_t v_a_28386__boxed_1831_; uint8_t v_val_28387__boxed_1832_; lean_object* v_res_1833_; 
v_a_28386__boxed_1831_ = lean_unbox(v_a_1820_);
v_val_28387__boxed_1832_ = lean_unbox(v_val_1821_);
v_res_1833_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_kind_1819_, v_a_28386__boxed_1831_, v_val_28387__boxed_1832_, v_as_1822_, v_as_x27_1823_, v_b_1824_, v_a_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_as_x27_1823_);
lean_dec(v_as_1822_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_x_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(v_00_u03b2_1838_, v_x_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec_ref(v_x_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5(lean_object* v_00_u03b2_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_x_1843_, v_x_1844_, v_x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(lean_object* v_00_u03c3_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_map_1849_, lean_object* v_init_1850_, lean_object* v_f_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_map_1849_, v_init_1850_, v_f_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1853_, lean_object* v_00_u03b2_1854_, lean_object* v_map_1855_, lean_object* v_init_1856_, lean_object* v_f_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(v_00_u03c3_1853_, v_00_u03b2_1854_, v_map_1855_, v_init_1856_, v_f_1857_);
lean_dec_ref(v_map_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(lean_object* v_00_u03c3_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_map_1861_, lean_object* v_f_1862_, lean_object* v_init_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_map_1861_, v_f_1862_, v_init_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___boxed(lean_object* v_00_u03c3_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_map_1867_, lean_object* v_f_1868_, lean_object* v_init_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(v_00_u03c3_1865_, v_00_u03b2_1866_, v_map_1867_, v_f_1868_, v_init_1869_);
lean_dec_ref(v_map_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(lean_object* v_00_u03b1_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v_msg_1872_, v___y_1873_, v___y_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b1_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(v_00_u03b1_1877_, v_msg_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(lean_object* v_00_u03b1_1883_, lean_object* v_preNode_1884_, lean_object* v_postNode_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1884_, v_postNode_1885_, v_x_1886_, v_x_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_preNode_1893_, lean_object* v_postNode_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(v_00_u03b1_1892_, v_preNode_1893_, v_postNode_1894_, v_x_1895_, v_x_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1901_, lean_object* v_x_1902_, size_t v_x_1903_, lean_object* v_x_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_1902_, v_x_1903_, v_x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
size_t v_x_28461__boxed_1910_; lean_object* v_res_1911_; 
v_x_28461__boxed_1910_ = lean_unbox_usize(v_x_1908_);
lean_dec(v_x_1908_);
v_res_1911_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(v_00_u03b2_1906_, v_x_1907_, v_x_28461__boxed_1910_, v_x_1909_);
lean_dec(v_x_1909_);
lean_dec_ref(v_x_1907_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1912_, lean_object* v_x_1913_, size_t v_x_1914_, size_t v_x_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_1913_, v_x_1914_, v_x_1915_, v_x_1916_, v_x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
size_t v_x_28472__boxed_1925_; size_t v_x_28473__boxed_1926_; lean_object* v_res_1927_; 
v_x_28472__boxed_1925_ = lean_unbox_usize(v_x_1921_);
lean_dec(v_x_1921_);
v_x_28473__boxed_1926_ = lean_unbox_usize(v_x_1922_);
lean_dec(v_x_1922_);
v_res_1927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(v_00_u03b2_1919_, v_x_1920_, v_x_28472__boxed_1925_, v_x_28473__boxed_1926_, v_x_1923_, v_x_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10___redArg(lean_object* v_map_1928_, lean_object* v_f_1929_, lean_object* v_init_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_1929_, v_map_1928_, v_init_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10(lean_object* v_00_u03c3_1932_, lean_object* v_00_u03c3_1933_, lean_object* v_00_u03b2_1934_, lean_object* v_map_1935_, lean_object* v_f_1936_, lean_object* v_init_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_1936_, v_map_1935_, v_init_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(lean_object* v_map_1939_, lean_object* v_f_1940_, lean_object* v_init_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_1940_, v_map_1939_, v_init_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_map_1943_, lean_object* v_f_1944_, lean_object* v_init_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(v_map_1943_, v_f_1944_, v_init_1945_);
lean_dec_ref(v_map_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(lean_object* v_00_u03c3_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_map_1949_, lean_object* v_f_1950_, lean_object* v_init_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_1950_, v_map_1949_, v_init_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03c3_1953_, lean_object* v_00_u03b2_1954_, lean_object* v_map_1955_, lean_object* v_f_1956_, lean_object* v_init_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(v_00_u03c3_1953_, v_00_u03b2_1954_, v_map_1955_, v_f_1956_, v_init_1957_);
lean_dec_ref(v_map_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(lean_object* v_msgData_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v_msgData_1959_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___boxed(lean_object* v_msgData_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(v_msgData_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(lean_object* v_00_u03b1_1969_, lean_object* v_preNode_1970_, lean_object* v_postNode_1971_, lean_object* v___x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1970_, v_postNode_1971_, v___x_1972_, v_x_1973_, v_x_1974_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_preNode_1980_, lean_object* v_postNode_1981_, lean_object* v___x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(v_00_u03b1_1979_, v_preNode_1980_, v_postNode_1981_, v___x_1982_, v_x_1983_, v_x_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1989_, lean_object* v_keys_1990_, lean_object* v_vals_1991_, lean_object* v_heq_1992_, lean_object* v_i_1993_, lean_object* v_k_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1990_, v_vals_1991_, v_i_1993_, v_k_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_1996_, lean_object* v_keys_1997_, lean_object* v_vals_1998_, lean_object* v_heq_1999_, lean_object* v_i_2000_, lean_object* v_k_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_1996_, v_keys_1997_, v_vals_1998_, v_heq_1999_, v_i_2000_, v_k_2001_);
lean_dec(v_k_2001_);
lean_dec_ref(v_vals_1998_);
lean_dec_ref(v_keys_1997_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18(lean_object* v_00_u03b2_2003_, lean_object* v_n_2004_, lean_object* v_k_2005_, lean_object* v_v_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(v_n_2004_, v_k_2005_, v_v_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(lean_object* v_00_u03b2_2008_, size_t v_depth_2009_, lean_object* v_keys_2010_, lean_object* v_vals_2011_, lean_object* v_heq_2012_, lean_object* v_i_2013_, lean_object* v_entries_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_depth_2009_, v_keys_2010_, v_vals_2011_, v_i_2013_, v_entries_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___boxed(lean_object* v_00_u03b2_2016_, lean_object* v_depth_2017_, lean_object* v_keys_2018_, lean_object* v_vals_2019_, lean_object* v_heq_2020_, lean_object* v_i_2021_, lean_object* v_entries_2022_){
_start:
{
size_t v_depth_boxed_2023_; lean_object* v_res_2024_; 
v_depth_boxed_2023_ = lean_unbox_usize(v_depth_2017_);
lean_dec(v_depth_2017_);
v_res_2024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(v_00_u03b2_2016_, v_depth_boxed_2023_, v_keys_2018_, v_vals_2019_, v_heq_2020_, v_i_2021_, v_entries_2022_);
lean_dec_ref(v_vals_2019_);
lean_dec_ref(v_keys_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22(lean_object* v_00_u03c3_2025_, lean_object* v_00_u03c3_2026_, lean_object* v_00_u03b1_2027_, lean_object* v_00_u03b2_2028_, lean_object* v_f_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_2029_, v_x_2030_, v_x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(lean_object* v_00_u03c3_2033_, lean_object* v_00_u03b1_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_f_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_2036_, v_x_2037_, v_x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___boxed(lean_object* v_00_u03c3_2040_, lean_object* v_00_u03b1_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_f_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(v_00_u03c3_2040_, v_00_u03b1_2041_, v_00_u03b2_2042_, v_f_2043_, v_x_2044_, v_x_2045_);
lean_dec_ref(v_x_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24(lean_object* v_00_u03b2_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(v_x_2048_, v_x_2049_, v_x_2050_, v_x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_00_u03c3_2055_, lean_object* v_00_u03c3_2056_, lean_object* v_f_2057_, lean_object* v_as_2058_, size_t v_i_2059_, size_t v_stop_2060_, lean_object* v_b_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_2057_, v_as_2058_, v_i_2059_, v_stop_2060_, v_b_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_00_u03c3_2065_, lean_object* v_00_u03c3_2066_, lean_object* v_f_2067_, lean_object* v_as_2068_, lean_object* v_i_2069_, lean_object* v_stop_2070_, lean_object* v_b_2071_){
_start:
{
size_t v_i_boxed_2072_; size_t v_stop_boxed_2073_; lean_object* v_res_2074_; 
v_i_boxed_2072_ = lean_unbox_usize(v_i_2069_);
lean_dec(v_i_2069_);
v_stop_boxed_2073_ = lean_unbox_usize(v_stop_2070_);
lean_dec(v_stop_2070_);
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(v_00_u03b1_2063_, v_00_u03b2_2064_, v_00_u03c3_2065_, v_00_u03c3_2066_, v_f_2067_, v_as_2068_, v_i_boxed_2072_, v_stop_boxed_2073_, v_b_2071_);
lean_dec_ref(v_as_2068_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(lean_object* v_00_u03c3_2075_, lean_object* v_00_u03c3_2076_, lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_f_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_heq_2082_, lean_object* v_i_2083_, lean_object* v_acc_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_2079_, v_keys_2080_, v_vals_2081_, v_i_2083_, v_acc_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___boxed(lean_object* v_00_u03c3_2086_, lean_object* v_00_u03c3_2087_, lean_object* v_00_u03b1_2088_, lean_object* v_00_u03b2_2089_, lean_object* v_f_2090_, lean_object* v_keys_2091_, lean_object* v_vals_2092_, lean_object* v_heq_2093_, lean_object* v_i_2094_, lean_object* v_acc_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(v_00_u03c3_2086_, v_00_u03c3_2087_, v_00_u03b1_2088_, v_00_u03b2_2089_, v_f_2090_, v_keys_2091_, v_vals_2092_, v_heq_2093_, v_i_2094_, v_acc_2095_);
lean_dec_ref(v_vals_2092_);
lean_dec_ref(v_keys_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(lean_object* v_00_u03b1_2097_, lean_object* v_00_u03b2_2098_, lean_object* v_00_u03c3_2099_, lean_object* v_f_2100_, lean_object* v_as_2101_, size_t v_i_2102_, size_t v_stop_2103_, lean_object* v_b_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_2100_, v_as_2101_, v_i_2102_, v_stop_2103_, v_b_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_00_u03c3_2108_, lean_object* v_f_2109_, lean_object* v_as_2110_, lean_object* v_i_2111_, lean_object* v_stop_2112_, lean_object* v_b_2113_){
_start:
{
size_t v_i_boxed_2114_; size_t v_stop_boxed_2115_; lean_object* v_res_2116_; 
v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_stop_boxed_2115_ = lean_unbox_usize(v_stop_2112_);
lean_dec(v_stop_2112_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(v_00_u03b1_2106_, v_00_u03b2_2107_, v_00_u03c3_2108_, v_f_2109_, v_as_2110_, v_i_boxed_2114_, v_stop_boxed_2115_, v_b_2113_);
lean_dec_ref(v_as_2110_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(lean_object* v_00_u03c3_2117_, lean_object* v_00_u03b1_2118_, lean_object* v_00_u03b2_2119_, lean_object* v_f_2120_, lean_object* v_keys_2121_, lean_object* v_vals_2122_, lean_object* v_heq_2123_, lean_object* v_i_2124_, lean_object* v_acc_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_2120_, v_keys_2121_, v_vals_2122_, v_i_2124_, v_acc_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2127_, lean_object* v_00_u03b1_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_f_2130_, lean_object* v_keys_2131_, lean_object* v_vals_2132_, lean_object* v_heq_2133_, lean_object* v_i_2134_, lean_object* v_acc_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(v_00_u03c3_2127_, v_00_u03b1_2128_, v_00_u03b2_2129_, v_f_2130_, v_keys_2131_, v_vals_2132_, v_heq_2133_, v_i_2134_, v_acc_2135_);
lean_dec_ref(v_vals_2132_);
lean_dec_ref(v_keys_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances));
v___x_2139_ = l_Lean_Elab_Command_addLinter(v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
return v_res_2141_;
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
