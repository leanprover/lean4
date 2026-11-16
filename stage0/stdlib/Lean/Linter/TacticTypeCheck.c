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
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_ctor_set(v___x_224_, 2, v___x_223_);
lean_ctor_set(v___x_224_, 3, v___x_223_);
lean_ctor_set(v___x_224_, 4, v___x_222_);
lean_ctor_set(v___x_224_, 5, v___x_222_);
lean_ctor_set(v___x_224_, 6, v___x_222_);
lean_ctor_set(v___x_224_, 7, v___x_222_);
lean_ctor_set(v___x_224_, 8, v___x_222_);
lean_ctor_set(v___x_224_, 9, v___x_222_);
lean_ctor_set(v___x_224_, 10, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(32u);
v___x_226_ = lean_mk_empty_array_with_capacity(v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4(void){
_start:
{
size_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_unsigned_to_nat(32u);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
v___x_232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__3);
v___x_233_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_229_);
lean_ctor_set(v___x_233_, 3, v___x_229_);
lean_ctor_set_usize(v___x_233_, 4, v___x_228_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_234_ = lean_box(1);
v___x_235_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_236_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_234_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(lean_object* v_msgData_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v_env_242_; uint8_t v___x_243_; lean_object* v_env_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_scopes_247_; lean_object* v___x_248_; lean_object* v_opts_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_241_ = lean_st_ref_get(v___y_239_);
v_env_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_env_242_);
lean_dec(v___x_241_);
v___x_243_ = 0;
v_env_244_ = l_Lean_Environment_setRecordingDeps(v_env_242_, v___x_243_);
v___x_245_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_246_ = lean_st_ref_get(v___y_239_);
v_scopes_247_ = lean_ctor_get(v___x_246_, 2);
lean_inc(v_scopes_247_);
lean_dec(v___x_246_);
v___x_248_ = l_List_head_x21___redArg(v___x_245_, v_scopes_247_);
lean_dec(v_scopes_247_);
v_opts_249_ = lean_ctor_get(v___x_248_, 1);
lean_inc_ref(v_opts_249_);
lean_dec(v___x_248_);
v___x_250_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__2);
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__5);
v___x_252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_252_, 0, v_env_244_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
lean_ctor_set(v___x_252_, 2, v___x_251_);
lean_ctor_set(v___x_252_, 3, v_opts_249_);
v___x_253_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v_msgData_238_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___boxed(lean_object* v_msgData_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v_msgData_255_, v___y_256_);
lean_dec(v___y_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(lean_object* v_ref_260_, lean_object* v_msgData_261_, uint8_t v_severity_262_, uint8_t v_isSilent_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___y_268_; uint8_t v___y_269_; lean_object* v___y_270_; uint8_t v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; uint8_t v___y_333_; lean_object* v___y_334_; uint8_t v___y_335_; lean_object* v___y_336_; uint8_t v___y_359_; uint8_t v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; uint8_t v___y_366_; uint8_t v___y_367_; uint8_t v___x_382_; uint8_t v___y_384_; uint8_t v___x_394_; 
v___x_382_ = 2;
v___x_394_ = l_Lean_instBEqMessageSeverity_beq(v_severity_262_, v___x_382_);
if (v___x_394_ == 0)
{
v___y_384_ = v___x_394_;
goto v___jp_383_;
}
else
{
uint8_t v___x_395_; 
lean_inc_ref(v_msgData_261_);
v___x_395_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_261_);
if (v___x_395_ == 0)
{
v___y_384_ = v___x_395_;
goto v___jp_383_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_msgData_261_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
v___jp_267_:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Elab_Command_getScope___redArg(v___y_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v_currNamespace_278_; lean_object* v___x_279_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v_currNamespace_278_ = lean_ctor_get(v_a_277_, 2);
lean_inc(v_currNamespace_278_);
lean_dec(v_a_277_);
v___x_279_ = l_Lean_Elab_Command_getScope___redArg(v___y_275_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_315_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_315_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_315_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_315_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_openDecls_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v_messages_290_; lean_object* v_scopes_291_; lean_object* v_usedQuotCtxts_292_; lean_object* v_nextMacroScope_293_; lean_object* v_maxRecDepth_294_; lean_object* v_ngen_295_; lean_object* v_auxDeclNGen_296_; lean_object* v_infoState_297_; lean_object* v_traceState_298_; lean_object* v_snapshotTasks_299_; lean_object* v_prevLinterStates_300_; lean_object* v_codeQualityEntryTasks_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_314_; 
v_openDecls_284_ = lean_ctor_get(v_a_280_, 3);
lean_inc(v_openDecls_284_);
lean_dec(v_a_280_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_currNamespace_278_);
lean_ctor_set(v___x_285_, 1, v_openDecls_284_);
v___x_286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___y_272_);
lean_inc_ref(v___y_270_);
lean_inc_ref(v___y_268_);
v___x_287_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_287_, 0, v___y_268_);
lean_ctor_set(v___x_287_, 1, v___y_274_);
lean_ctor_set(v___x_287_, 2, v___y_273_);
lean_ctor_set(v___x_287_, 3, v___y_270_);
lean_ctor_set(v___x_287_, 4, v___x_286_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*5, v___y_269_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*5 + 1, v___y_271_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*5 + 2, v_isSilent_263_);
v___x_288_ = lean_st_ref_take(v___y_275_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
v_messages_290_ = lean_ctor_get(v___x_288_, 1);
v_scopes_291_ = lean_ctor_get(v___x_288_, 2);
v_usedQuotCtxts_292_ = lean_ctor_get(v___x_288_, 3);
v_nextMacroScope_293_ = lean_ctor_get(v___x_288_, 4);
v_maxRecDepth_294_ = lean_ctor_get(v___x_288_, 5);
v_ngen_295_ = lean_ctor_get(v___x_288_, 6);
v_auxDeclNGen_296_ = lean_ctor_get(v___x_288_, 7);
v_infoState_297_ = lean_ctor_get(v___x_288_, 8);
v_traceState_298_ = lean_ctor_get(v___x_288_, 9);
v_snapshotTasks_299_ = lean_ctor_get(v___x_288_, 10);
v_prevLinterStates_300_ = lean_ctor_get(v___x_288_, 11);
v_codeQualityEntryTasks_301_ = lean_ctor_get(v___x_288_, 12);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_314_ == 0)
{
v___x_303_ = v___x_288_;
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_codeQualityEntryTasks_301_);
lean_inc(v_prevLinterStates_300_);
lean_inc(v_snapshotTasks_299_);
lean_inc(v_traceState_298_);
lean_inc(v_infoState_297_);
lean_inc(v_auxDeclNGen_296_);
lean_inc(v_ngen_295_);
lean_inc(v_maxRecDepth_294_);
lean_inc(v_nextMacroScope_293_);
lean_inc(v_usedQuotCtxts_292_);
lean_inc(v_scopes_291_);
lean_inc(v_messages_290_);
lean_inc(v_env_289_);
lean_dec(v___x_288_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = lean_box(0);
v___x_306_ = l_Lean_MessageLog_add(v___x_287_, v_messages_290_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_env_289_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_scopes_291_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_usedQuotCtxts_292_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_nextMacroScope_293_);
lean_ctor_set(v_reuseFailAlloc_313_, 5, v_maxRecDepth_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 6, v_ngen_295_);
lean_ctor_set(v_reuseFailAlloc_313_, 7, v_auxDeclNGen_296_);
lean_ctor_set(v_reuseFailAlloc_313_, 8, v_infoState_297_);
lean_ctor_set(v_reuseFailAlloc_313_, 9, v_traceState_298_);
lean_ctor_set(v_reuseFailAlloc_313_, 10, v_snapshotTasks_299_);
lean_ctor_set(v_reuseFailAlloc_313_, 11, v_prevLinterStates_300_);
lean_ctor_set(v_reuseFailAlloc_313_, 12, v_codeQualityEntryTasks_301_);
v___x_308_ = v_reuseFailAlloc_313_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_st_ref_put(v___y_275_, v___x_308_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_305_);
v___x_311_ = v___x_282_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_305_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_currNamespace_278_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
v_a_316_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_279_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_279_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
v_a_324_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_276_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_276_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v___jp_332_:
{
lean_object* v_fileName_337_; lean_object* v_fileMap_338_; uint8_t v_suppressElabErrors_339_; lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_357_; 
v_fileName_337_ = lean_ctor_get(v___y_264_, 0);
v_fileMap_338_ = lean_ctor_get(v___y_264_, 1);
v_suppressElabErrors_339_ = lean_ctor_get_uint8(v___y_264_, sizeof(void*)*10);
v___x_340_ = lean_box(v_suppressElabErrors_339_);
v___f_341_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___lam__0___boxed), 2, 1);
lean_closure_set(v___f_341_, 0, v___x_340_);
v___x_342_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_261_);
v___x_343_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v___x_342_, v___y_265_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_357_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_357_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_357_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_inc_ref_n(v_fileMap_338_, 2);
v___x_348_ = l_Lean_FileMap_toPosition(v_fileMap_338_, v___y_334_);
lean_dec(v___y_334_);
v___x_349_ = l_Lean_FileMap_toPosition(v_fileMap_338_, v___y_336_);
lean_dec(v___y_336_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___closed__0));
if (v_suppressElabErrors_339_ == 0)
{
lean_del_object(v___x_346_);
lean_dec_ref(v___f_341_);
v___y_268_ = v_fileName_337_;
v___y_269_ = v___y_333_;
v___y_270_ = v___x_351_;
v___y_271_ = v___y_335_;
v___y_272_ = v_a_344_;
v___y_273_ = v___x_350_;
v___y_274_ = v___x_348_;
v___y_275_ = v___y_265_;
goto v___jp_267_;
}
else
{
uint8_t v___x_352_; 
lean_inc(v_a_344_);
v___x_352_ = l_Lean_MessageData_hasTag(v___f_341_, v_a_344_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_355_; 
lean_dec_ref_known(v___x_350_, 1);
lean_dec_ref(v___x_348_);
lean_dec(v_a_344_);
v___x_353_ = lean_box(0);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_353_);
v___x_355_ = v___x_346_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
else
{
lean_del_object(v___x_346_);
v___y_268_ = v_fileName_337_;
v___y_269_ = v___y_333_;
v___y_270_ = v___x_351_;
v___y_271_ = v___y_335_;
v___y_272_ = v_a_344_;
v___y_273_ = v___x_350_;
v___y_274_ = v___x_348_;
v___y_275_ = v___y_265_;
goto v___jp_267_;
}
}
}
}
v___jp_358_:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Syntax_getTailPos_x3f(v___y_361_, v___y_359_);
lean_dec(v___y_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_inc(v___y_362_);
v___y_333_ = v___y_359_;
v___y_334_ = v___y_362_;
v___y_335_ = v___y_360_;
v___y_336_ = v___y_362_;
goto v___jp_332_;
}
else
{
lean_object* v_val_364_; 
v_val_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v___x_363_, 1);
v___y_333_ = v___y_359_;
v___y_334_ = v___y_362_;
v___y_335_ = v___y_360_;
v___y_336_ = v_val_364_;
goto v___jp_332_;
}
}
v___jp_365_:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Elab_Command_getRef___redArg(v___y_264_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v_ref_370_; lean_object* v___x_371_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v_ref_370_ = l_Lean_replaceRef(v_ref_260_, v_a_369_);
lean_dec(v_a_369_);
v___x_371_ = l_Lean_Syntax_getPos_x3f(v_ref_370_, v___y_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_372_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___y_359_ = v___y_366_;
v___y_360_ = v___y_367_;
v___y_361_ = v_ref_370_;
v___y_362_ = v___x_372_;
goto v___jp_358_;
}
else
{
lean_object* v_val_373_; 
v_val_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_371_, 1);
v___y_359_ = v___y_366_;
v___y_360_ = v___y_367_;
v___y_361_ = v_ref_370_;
v___y_362_ = v_val_373_;
goto v___jp_358_;
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_msgData_261_);
v_a_374_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_368_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_scopes_387_; lean_object* v___x_388_; lean_object* v_opts_389_; uint8_t v___x_390_; uint8_t v___x_391_; 
v___x_385_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_386_ = lean_st_ref_get(v___y_265_);
v_scopes_387_ = lean_ctor_get(v___x_386_, 2);
lean_inc(v_scopes_387_);
lean_dec(v___x_386_);
v___x_388_ = l_List_head_x21___redArg(v___x_385_, v_scopes_387_);
lean_dec(v_scopes_387_);
v_opts_389_ = lean_ctor_get(v___x_388_, 1);
lean_inc_ref(v_opts_389_);
lean_dec(v___x_388_);
v___x_390_ = 1;
v___x_391_ = l_Lean_instBEqMessageSeverity_beq(v_severity_262_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_opts_389_);
v___y_366_ = v___y_384_;
v___y_367_ = v_severity_262_;
goto v___jp_365_;
}
else
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = l_Lean_warningAsError;
v___x_393_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_389_, v___x_392_);
lean_dec_ref(v_opts_389_);
if (v___x_393_ == 0)
{
v___y_366_ = v___y_384_;
v___y_367_ = v_severity_262_;
goto v___jp_365_;
}
else
{
v___y_366_ = v___y_384_;
v___y_367_ = v___x_382_;
goto v___jp_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20___boxed(lean_object* v_ref_398_, lean_object* v_msgData_399_, lean_object* v_severity_400_, lean_object* v_isSilent_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
uint8_t v_severity_boxed_405_; uint8_t v_isSilent_boxed_406_; lean_object* v_res_407_; 
v_severity_boxed_405_ = lean_unbox(v_severity_400_);
v_isSilent_boxed_406_ = lean_unbox(v_isSilent_401_);
v_res_407_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(v_ref_398_, v_msgData_399_, v_severity_boxed_405_, v_isSilent_boxed_406_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v_ref_398_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(lean_object* v_ref_408_, lean_object* v_msgData_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; 
v___x_413_ = 1;
v___x_414_ = 0;
v___x_415_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20(v_ref_408_, v_msgData_409_, v___x_413_, v___x_414_, v___y_410_, v___y_411_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15___boxed(lean_object* v_ref_416_, lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(v_ref_416_, v_msgData_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v_ref_416_);
return v_res_421_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__0));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__2));
v___x_427_ = l_Lean_stringToMessageData(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(lean_object* v_linterOption_428_, lean_object* v_stx_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_name_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_452_; 
v_name_434_ = lean_ctor_get(v_linterOption_428_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v_linterOption_428_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v_linterOption_428_, 1);
lean_dec(v_unused_453_);
v___x_436_ = v_linterOption_428_;
v_isShared_437_ = v_isSharedCheck_452_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_name_434_);
lean_dec(v_linterOption_428_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_452_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__1);
lean_inc(v_name_434_);
v___x_439_ = l_Lean_MessageData_ofName(v_name_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 7);
lean_ctor_set(v___x_436_, 1, v___x_439_);
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_439_);
v___x_441_ = v_reuseFailAlloc_451_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_disable_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_442_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___closed__3);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v_disable_444_ = l_Lean_MessageData_note(v___x_443_);
v___x_445_ = l_Lean_Linter_linterMessageTag;
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v_msg_430_);
lean_ctor_set(v___x_446_, 1, v_disable_444_);
v___x_447_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_448_, 0, v_name_434_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_inc(v_stx_429_);
v___x_449_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_449_, 0, v_stx_429_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15(v_stx_429_, v___x_449_, v___y_431_, v___y_432_);
lean_dec(v_stx_429_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object* v_linterOption_454_, lean_object* v_stx_455_, lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_linterOption_454_, v_stx_455_, v_msg_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(lean_object* v_o_463_, lean_object* v_k_464_, uint8_t v_v_465_){
_start:
{
lean_object* v_map_466_; uint8_t v_hasTrace_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_481_; 
v_map_466_ = lean_ctor_get(v_o_463_, 0);
v_hasTrace_467_ = lean_ctor_get_uint8(v_o_463_, sizeof(void*)*1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_o_463_);
if (v_isSharedCheck_481_ == 0)
{
v___x_469_ = v_o_463_;
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_map_466_);
lean_dec(v_o_463_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_471_, 0, v_v_465_);
lean_inc(v_k_464_);
v___x_472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_464_, v___x_471_, v_map_466_);
if (v_hasTrace_467_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_476_; 
v___x_473_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___closed__0));
v___x_474_ = l_Lean_Name_isPrefixOf(v___x_473_, v_k_464_);
lean_dec(v_k_464_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_476_ = v___x_469_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_472_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*1, v___x_474_);
return v___x_476_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v_k_464_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_479_ = v___x_469_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_480_, sizeof(void*)*1, v_hasTrace_467_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11___boxed(lean_object* v_o_482_, lean_object* v_k_483_, lean_object* v_v_484_){
_start:
{
uint8_t v_v_boxed_485_; lean_object* v_res_486_; 
v_v_boxed_485_ = lean_unbox(v_v_484_);
v_res_486_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(v_o_482_, v_k_483_, v_v_boxed_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object* v_opts_487_, lean_object* v_opt_488_, uint8_t v_val_489_){
_start:
{
lean_object* v_name_490_; lean_object* v___x_491_; 
v_name_490_ = lean_ctor_get(v_opt_488_, 0);
lean_inc(v_name_490_);
lean_dec_ref(v_opt_488_);
v___x_491_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__11(v_opts_487_, v_name_490_, v_val_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object* v_opts_492_, lean_object* v_opt_493_, lean_object* v_val_494_){
_start:
{
uint8_t v_val_boxed_495_; lean_object* v_res_496_; 
v_val_boxed_495_ = lean_unbox(v_val_494_);
v_res_496_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_opts_492_, v_opt_493_, v_val_boxed_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_i_499_, lean_object* v_k_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_array_get_size(v_keys_497_);
v___x_502_ = lean_nat_dec_lt(v_i_499_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v_i_499_);
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v_k_x27_504_; uint8_t v___x_505_; 
v_k_x27_504_ = lean_array_fget_borrowed(v_keys_497_, v_i_499_);
v___x_505_ = lean_name_eq(v_k_500_, v_k_x27_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_i_499_, v___x_506_);
lean_dec(v_i_499_);
v_i_499_ = v___x_507_;
goto _start;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_array_fget_borrowed(v_vals_498_, v_i_499_);
lean_dec(v_i_499_);
lean_inc(v___x_509_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_i_513_, lean_object* v_k_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_511_, v_vals_512_, v_i_513_, v_k_514_);
lean_dec(v_k_514_);
lean_dec_ref(v_vals_512_);
lean_dec_ref(v_keys_511_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(lean_object* v_x_516_, size_t v_x_517_, lean_object* v_x_518_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_es_519_; lean_object* v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_j_523_; lean_object* v___x_524_; 
v_es_519_ = lean_ctor_get(v_x_516_, 0);
v___x_520_ = lean_box(2);
v___x_521_ = ((size_t)31ULL);
v___x_522_ = lean_usize_land(v_x_517_, v___x_521_);
v_j_523_ = lean_usize_to_nat(v___x_522_);
v___x_524_ = lean_array_get_borrowed(v___x_520_, v_es_519_, v_j_523_);
lean_dec(v_j_523_);
switch(lean_obj_tag(v___x_524_))
{
case 0:
{
lean_object* v_key_525_; lean_object* v_val_526_; uint8_t v___x_527_; 
v_key_525_ = lean_ctor_get(v___x_524_, 0);
v_val_526_ = lean_ctor_get(v___x_524_, 1);
v___x_527_ = lean_name_eq(v_x_518_, v_key_525_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
lean_inc(v_val_526_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_val_526_);
return v___x_529_;
}
}
case 1:
{
lean_object* v_node_530_; size_t v___x_531_; size_t v___x_532_; 
v_node_530_ = lean_ctor_get(v___x_524_, 0);
v___x_531_ = ((size_t)5ULL);
v___x_532_ = lean_usize_shift_right(v_x_517_, v___x_531_);
v_x_516_ = v_node_530_;
v_x_517_ = v___x_532_;
goto _start;
}
default: 
{
lean_object* v___x_534_; 
v___x_534_ = lean_box(0);
return v___x_534_;
}
}
}
else
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_ks_535_ = lean_ctor_get(v_x_516_, 0);
v_vs_536_ = lean_ctor_get(v_x_516_, 1);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_535_, v_vs_536_, v___x_537_, v_x_518_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
size_t v_x_26353__boxed_542_; lean_object* v_res_543_; 
v_x_26353__boxed_542_ = lean_unbox_usize(v_x_540_);
lean_dec(v_x_540_);
v_res_543_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_539_, v_x_26353__boxed_542_, v_x_541_);
lean_dec(v_x_541_);
lean_dec_ref(v_x_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
uint64_t v___y_547_; 
if (lean_obj_tag(v_x_545_) == 0)
{
uint64_t v___x_550_; 
v___x_550_ = 1723ULL;
v___y_547_ = v___x_550_;
goto v___jp_546_;
}
else
{
uint64_t v_hash_551_; 
v_hash_551_ = lean_ctor_get_uint64(v_x_545_, sizeof(void*)*2);
v___y_547_ = v_hash_551_;
goto v___jp_546_;
}
v___jp_546_:
{
size_t v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_uint64_to_usize(v___y_547_);
v___x_549_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_544_, v___x_548_, v_x_545_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg___boxed(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_x_552_, v_x_553_);
lean_dec(v_x_553_);
lean_dec_ref(v_x_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_ks_559_; lean_object* v_vs_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_584_; 
v_ks_559_ = lean_ctor_get(v_x_555_, 0);
v_vs_560_ = lean_ctor_get(v_x_555_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_584_ == 0)
{
v___x_562_ = v_x_555_;
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_vs_560_);
lean_inc(v_ks_559_);
lean_dec(v_x_555_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_584_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_array_get_size(v_ks_559_);
v___x_565_ = lean_nat_dec_lt(v_x_556_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec(v_x_556_);
v___x_566_ = lean_array_push(v_ks_559_, v_x_557_);
v___x_567_ = lean_array_push(v_vs_560_, v_x_558_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_567_);
lean_ctor_set(v___x_562_, 0, v___x_566_);
v___x_569_ = v___x_562_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v_k_x27_571_; uint8_t v___x_572_; 
v_k_x27_571_ = lean_array_fget_borrowed(v_ks_559_, v_x_556_);
v___x_572_ = lean_name_eq(v_x_557_, v_k_x27_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_574_; 
if (v_isShared_563_ == 0)
{
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_ks_559_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_vs_560_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_x_556_, v___x_575_);
lean_dec(v_x_556_);
v_x_555_ = v___x_574_;
v_x_556_ = v___x_576_;
goto _start;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_array_fset(v_ks_559_, v_x_556_, v_x_557_);
v___x_580_ = lean_array_fset(v_vs_560_, v_x_556_, v_x_558_);
lean_dec(v_x_556_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_580_);
lean_ctor_set(v___x_562_, 0, v___x_579_);
v___x_582_ = v___x_562_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(lean_object* v_n_585_, lean_object* v_k_586_, lean_object* v_v_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(v_n_585_, v___x_588_, v_k_586_, v_v_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(lean_object* v_x_591_, size_t v_x_592_, size_t v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v_es_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v_j_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_es_596_ = lean_ctor_get(v_x_591_, 0);
v___x_597_ = ((size_t)31ULL);
v___x_598_ = lean_usize_land(v_x_592_, v___x_597_);
v_j_599_ = lean_usize_to_nat(v___x_598_);
v___x_600_ = lean_array_get_size(v_es_596_);
v___x_601_ = lean_nat_dec_lt(v_j_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_j_599_);
lean_dec(v_x_595_);
lean_dec(v_x_594_);
return v_x_591_;
}
else
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_640_; 
lean_inc_ref(v_es_596_);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v_x_591_, 0);
lean_dec(v_unused_641_);
v___x_603_ = v_x_591_;
v_isShared_604_ = v_isSharedCheck_640_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_x_591_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_640_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_v_605_; lean_object* v___x_606_; lean_object* v_xs_x27_607_; lean_object* v___y_609_; 
v_v_605_ = lean_array_fget(v_es_596_, v_j_599_);
v___x_606_ = lean_box(0);
v_xs_x27_607_ = lean_array_fset(v_es_596_, v_j_599_, v___x_606_);
switch(lean_obj_tag(v_v_605_))
{
case 0:
{
lean_object* v_key_614_; lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_625_; 
v_key_614_ = lean_ctor_get(v_v_605_, 0);
v_val_615_ = lean_ctor_get(v_v_605_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_v_605_);
if (v_isSharedCheck_625_ == 0)
{
v___x_617_ = v_v_605_;
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_inc(v_key_614_);
lean_dec(v_v_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_name_eq(v_x_594_, v_key_614_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_del_object(v___x_617_);
v___x_620_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_614_, v_val_615_, v_x_594_, v_x_595_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___y_609_ = v___x_621_;
goto v___jp_608_;
}
else
{
lean_object* v___x_623_; 
lean_dec(v_val_615_);
lean_dec(v_key_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v_x_595_);
lean_ctor_set(v___x_617_, 0, v_x_594_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_x_594_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_x_595_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v___y_609_ = v___x_623_;
goto v___jp_608_;
}
}
}
}
case 1:
{
lean_object* v_node_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_638_; 
v_node_626_ = lean_ctor_get(v_v_605_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_v_605_);
if (v_isSharedCheck_638_ == 0)
{
v___x_628_ = v_v_605_;
v_isShared_629_ = v_isSharedCheck_638_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_node_626_);
lean_dec(v_v_605_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_638_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_630_ = ((size_t)5ULL);
v___x_631_ = lean_usize_shift_right(v_x_592_, v___x_630_);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_x_593_, v___x_632_);
v___x_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_node_626_, v___x_631_, v___x_633_, v_x_594_, v_x_595_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_634_);
v___x_636_ = v___x_628_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v___y_609_ = v___x_636_;
goto v___jp_608_;
}
}
}
default: 
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_x_594_);
lean_ctor_set(v___x_639_, 1, v_x_595_);
v___y_609_ = v___x_639_;
goto v___jp_608_;
}
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_array_fset(v_xs_x27_607_, v_j_599_, v___y_609_);
lean_dec(v_j_599_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_610_);
v___x_612_ = v___x_603_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_object* v_ks_642_; lean_object* v_vs_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_661_; 
v_ks_642_ = lean_ctor_get(v_x_591_, 0);
v_vs_643_ = lean_ctor_get(v_x_591_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_661_ == 0)
{
v___x_645_ = v_x_591_;
v_isShared_646_ = v_isSharedCheck_661_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_vs_643_);
lean_inc(v_ks_642_);
lean_dec(v_x_591_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_661_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_ks_642_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_vs_643_);
v___x_648_ = v_reuseFailAlloc_660_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v_newNode_649_; size_t v___x_650_; uint8_t v___x_651_; 
v_newNode_649_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(v___x_648_, v_x_594_, v_x_595_);
v___x_650_ = ((size_t)7ULL);
v___x_651_ = lean_usize_dec_le(v___x_650_, v_x_593_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_649_);
v___x_653_ = lean_unsigned_to_nat(4u);
v___x_654_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v_ks_655_; lean_object* v_vs_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_ks_655_ = lean_ctor_get(v_newNode_649_, 0);
lean_inc_ref(v_ks_655_);
v_vs_656_ = lean_ctor_get(v_newNode_649_, 1);
lean_inc_ref(v_vs_656_);
lean_dec_ref(v_newNode_649_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___closed__0);
v___x_659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_x_593_, v_ks_655_, v_vs_656_, v___x_657_, v___x_658_);
lean_dec_ref(v_vs_656_);
lean_dec_ref(v_ks_655_);
return v___x_659_;
}
else
{
return v_newNode_649_;
}
}
else
{
return v_newNode_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(size_t v_depth_662_, lean_object* v_keys_663_, lean_object* v_vals_664_, lean_object* v_i_665_, lean_object* v_entries_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_array_get_size(v_keys_663_);
v___x_668_ = lean_nat_dec_lt(v_i_665_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_i_665_);
return v_entries_666_;
}
else
{
lean_object* v_k_669_; lean_object* v_v_670_; uint64_t v___y_672_; 
v_k_669_ = lean_array_fget_borrowed(v_keys_663_, v_i_665_);
v_v_670_ = lean_array_fget_borrowed(v_vals_664_, v_i_665_);
if (lean_obj_tag(v_k_669_) == 0)
{
uint64_t v___x_683_; 
v___x_683_ = 1723ULL;
v___y_672_ = v___x_683_;
goto v___jp_671_;
}
else
{
uint64_t v_hash_684_; 
v_hash_684_ = lean_ctor_get_uint64(v_k_669_, sizeof(void*)*2);
v___y_672_ = v_hash_684_;
goto v___jp_671_;
}
v___jp_671_:
{
size_t v_h_673_; size_t v___x_674_; lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; size_t v___x_678_; size_t v_h_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_h_673_ = lean_uint64_to_usize(v___y_672_);
v___x_674_ = ((size_t)5ULL);
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_sub(v_depth_662_, v___x_676_);
v___x_678_ = lean_usize_mul(v___x_674_, v___x_677_);
v_h_679_ = lean_usize_shift_right(v_h_673_, v___x_678_);
v___x_680_ = lean_nat_add(v_i_665_, v___x_675_);
lean_dec(v_i_665_);
lean_inc(v_v_670_);
lean_inc(v_k_669_);
v___x_681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_entries_666_, v_h_679_, v_depth_662_, v_k_669_, v_v_670_);
v_i_665_ = v___x_680_;
v_entries_666_ = v___x_681_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg___boxed(lean_object* v_depth_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_i_688_, lean_object* v_entries_689_){
_start:
{
size_t v_depth_boxed_690_; lean_object* v_res_691_; 
v_depth_boxed_690_ = lean_unbox_usize(v_depth_685_);
lean_dec(v_depth_685_);
v_res_691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_depth_boxed_690_, v_keys_686_, v_vals_687_, v_i_688_, v_entries_689_);
lean_dec_ref(v_vals_687_);
lean_dec_ref(v_keys_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
size_t v_x_26494__boxed_697_; size_t v_x_26495__boxed_698_; lean_object* v_res_699_; 
v_x_26494__boxed_697_ = lean_unbox_usize(v_x_693_);
lean_dec(v_x_693_);
v_x_26495__boxed_698_ = lean_unbox_usize(v_x_694_);
lean_dec(v_x_694_);
v_res_699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_692_, v_x_26494__boxed_697_, v_x_26495__boxed_698_, v_x_695_, v_x_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
uint64_t v___y_704_; 
if (lean_obj_tag(v_x_701_) == 0)
{
uint64_t v___x_708_; 
v___x_708_ = 1723ULL;
v___y_704_ = v___x_708_;
goto v___jp_703_;
}
else
{
uint64_t v_hash_709_; 
v_hash_709_ = lean_ctor_get_uint64(v_x_701_, sizeof(void*)*2);
v___y_704_ = v_hash_709_;
goto v___jp_703_;
}
v___jp_703_:
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_uint64_to_usize(v___y_704_);
v___x_706_ = ((size_t)1ULL);
v___x_707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_700_, v___x_705_, v___x_706_, v_x_701_, v_x_702_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(lean_object* v_oldCounters_710_, lean_object* v_x_711_, lean_object* v_____s_712_){
_start:
{
lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; 
v_fst_713_ = lean_ctor_get(v_x_711_, 0);
lean_inc(v_fst_713_);
v_snd_714_ = lean_ctor_get(v_x_711_, 1);
lean_inc(v_snd_714_);
lean_dec_ref(v_x_711_);
v___x_715_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_oldCounters_710_, v_fst_713_);
if (lean_obj_tag(v___x_715_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
v_val_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v_result_721_; lean_object* v___x_723_; 
v___x_720_ = lean_nat_sub(v_snd_714_, v_val_716_);
lean_dec(v_val_716_);
lean_dec(v_snd_714_);
v_result_721_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_____s_712_, v_fst_713_, v___x_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_result_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_result_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_result_726_; lean_object* v___x_727_; 
lean_dec(v___x_715_);
v_result_726_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_____s_712_, v_fst_713_, v_snd_714_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_result_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed(lean_object* v_oldCounters_728_, lean_object* v_x_729_, lean_object* v_____s_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0(v_oldCounters_728_, v_x_729_, v_____s_730_);
lean_dec_ref(v_oldCounters_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0(lean_object* v_f_732_, lean_object* v_s_733_, lean_object* v_a_734_, lean_object* v_b_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_a_734_);
lean_ctor_set(v___x_736_, 1, v_b_735_);
v___x_737_ = lean_apply_2(v_f_732_, v___x_736_, v_s_733_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
v_a_746_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_737_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(lean_object* v_f_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_i_757_, lean_object* v_acc_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_keys_755_);
v___x_760_ = lean_nat_dec_lt(v_i_757_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v_i_757_);
lean_dec_ref(v_f_754_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_acc_758_);
return v___x_761_;
}
else
{
lean_object* v_k_762_; lean_object* v_v_763_; lean_object* v___x_764_; 
v_k_762_ = lean_array_fget_borrowed(v_keys_755_, v_i_757_);
v_v_763_ = lean_array_fget_borrowed(v_vals_756_, v_i_757_);
lean_inc_ref(v_f_754_);
lean_inc(v_v_763_);
lean_inc(v_k_762_);
v___x_764_ = lean_apply_3(v_f_754_, v_acc_758_, v_k_762_, v_v_763_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_dec(v_i_757_);
lean_dec_ref(v_f_754_);
return v___x_764_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_add(v_i_757_, v___x_766_);
lean_dec(v_i_757_);
v_i_757_ = v___x_767_;
v_acc_758_ = v_a_765_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg___boxed(lean_object* v_f_769_, lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_i_772_, lean_object* v_acc_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_769_, v_keys_770_, v_vals_771_, v_i_772_, v_acc_773_);
lean_dec_ref(v_vals_771_);
lean_dec_ref(v_keys_770_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(lean_object* v_f_775_, lean_object* v_as_776_, size_t v_i_777_, size_t v_stop_778_, lean_object* v_b_779_){
_start:
{
lean_object* v_a_781_; lean_object* v___y_786_; uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_eq(v_i_777_, v_stop_778_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_array_uget_borrowed(v_as_776_, v_i_777_);
switch(lean_obj_tag(v___x_789_))
{
case 0:
{
lean_object* v_key_790_; lean_object* v_val_791_; lean_object* v___x_792_; 
v_key_790_ = lean_ctor_get(v___x_789_, 0);
v_val_791_ = lean_ctor_get(v___x_789_, 1);
lean_inc_ref(v_f_775_);
lean_inc(v_val_791_);
lean_inc(v_key_790_);
v___x_792_ = lean_apply_3(v_f_775_, v_b_779_, v_key_790_, v_val_791_);
v___y_786_ = v___x_792_;
goto v___jp_785_;
}
case 1:
{
lean_object* v_node_793_; lean_object* v___x_794_; 
v_node_793_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_node_793_);
lean_inc_ref(v_f_775_);
v___x_794_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_775_, v_node_793_, v_b_779_);
v___y_786_ = v___x_794_;
goto v___jp_785_;
}
default: 
{
v_a_781_ = v_b_779_;
goto v___jp_780_;
}
}
}
else
{
lean_object* v___x_795_; 
lean_dec_ref(v_f_775_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v_b_779_);
return v___x_795_;
}
v___jp_780_:
{
size_t v___x_782_; size_t v___x_783_; 
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_add(v_i_777_, v___x_782_);
v_i_777_ = v___x_783_;
v_b_779_ = v_a_781_;
goto _start;
}
v___jp_785_:
{
if (lean_obj_tag(v___y_786_) == 0)
{
lean_dec_ref(v_f_775_);
return v___y_786_;
}
else
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___y_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___y_786_, 1);
v_a_781_ = v_a_787_;
goto v___jp_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(lean_object* v_f_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_es_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_812_; 
v_es_799_ = lean_ctor_get(v_x_797_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_812_ == 0)
{
v___x_801_ = v_x_797_;
v_isShared_802_ = v_isSharedCheck_812_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_es_799_);
lean_dec(v_x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_812_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_array_get_size(v_es_799_);
v___x_805_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref(v_es_799_);
lean_dec_ref(v_f_796_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v_x_798_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_x_798_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
lean_del_object(v___x_801_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_804_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_796_, v_es_799_, v___x_809_, v___x_810_, v_x_798_);
lean_dec_ref(v_es_799_);
return v___x_811_;
}
}
}
else
{
lean_object* v_ks_813_; lean_object* v_vs_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_ks_813_ = lean_ctor_get(v_x_797_, 0);
lean_inc_ref(v_ks_813_);
v_vs_814_ = lean_ctor_get(v_x_797_, 1);
lean_inc_ref(v_vs_814_);
lean_dec_ref_known(v_x_797_, 2);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_796_, v_ks_813_, v_vs_814_, v___x_815_, v_x_798_);
lean_dec_ref(v_vs_814_);
lean_dec_ref(v_ks_813_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg___boxed(lean_object* v_f_817_, lean_object* v_as_818_, lean_object* v_i_819_, lean_object* v_stop_820_, lean_object* v_b_821_){
_start:
{
size_t v_i_boxed_822_; size_t v_stop_boxed_823_; lean_object* v_res_824_; 
v_i_boxed_822_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_stop_boxed_823_ = lean_unbox_usize(v_stop_820_);
lean_dec(v_stop_820_);
v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_817_, v_as_818_, v_i_boxed_822_, v_stop_boxed_823_, v_b_821_);
lean_dec_ref(v_as_818_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(lean_object* v_map_825_, lean_object* v_init_826_, lean_object* v_f_827_){
_start:
{
lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v_a_830_; 
v___f_828_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___lam__0), 4, 1);
lean_closure_set(v___f_828_, 0, v_f_827_);
lean_inc_ref(v_map_825_);
v___x_829_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v___f_828_, v_map_825_, v_init_826_);
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_829_);
return v_a_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg___boxed(lean_object* v_map_831_, lean_object* v_init_832_, lean_object* v_f_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_map_831_, v_init_832_, v_f_833_);
lean_dec_ref(v_map_831_);
return v_res_834_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0(void){
_start:
{
lean_object* v___x_835_; lean_object* v_result_836_; 
v___x_835_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v_result_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_result_836_, 0, v___x_835_);
return v_result_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object* v_newCounters_837_, lean_object* v_oldCounters_838_){
_start:
{
lean_object* v___f_839_; lean_object* v_result_840_; lean_object* v___x_841_; 
v___f_839_ = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___lam__0___boxed), 3, 1);
lean_closure_set(v___f_839_, 0, v_oldCounters_838_);
v_result_840_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___closed__0);
v___x_841_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_newCounters_837_, v_result_840_, v___f_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object* v_newCounters_842_, lean_object* v_oldCounters_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_newCounters_842_, v_oldCounters_843_);
lean_dec_ref(v_newCounters_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object* v___x_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
if (lean_obj_tag(v_a_846_) == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v___x_845_);
v___x_848_ = lean_array_to_list(v_a_847_);
return v___x_848_;
}
else
{
lean_object* v_head_849_; lean_object* v_tail_850_; lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_head_849_ = lean_ctor_get(v_a_846_, 0);
lean_inc(v_head_849_);
v_tail_850_ = lean_ctor_get(v_a_846_, 1);
lean_inc(v_tail_850_);
lean_dec_ref_known(v_a_846_, 2);
v_fst_851_ = lean_ctor_get(v_head_849_, 0);
lean_inc(v_fst_851_);
v_snd_852_ = lean_ctor_get(v_head_849_, 1);
lean_inc(v_snd_852_);
lean_dec(v_head_849_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_nat_dec_lt(v___x_853_, v_snd_852_);
lean_dec(v_snd_852_);
if (v___x_854_ == 0)
{
lean_dec(v_fst_851_);
v_a_846_ = v_tail_850_;
goto _start;
}
else
{
uint8_t v___x_856_; 
lean_inc(v_fst_851_);
lean_inc_ref(v___x_845_);
v___x_856_ = l_Lean_getReducibilityStatusCore(v___x_845_, v_fst_851_);
if (v___x_856_ == 1)
{
uint8_t v___x_857_; 
lean_inc_ref(v___x_845_);
v___x_857_ = l_Lean_Meta_isInstanceCore(v___x_845_, v_fst_851_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = l_Lean_MessageData_ofConstName(v_fst_851_, v___x_857_);
v___x_859_ = lean_array_push(v_a_847_, v___x_858_);
v_a_846_ = v_tail_850_;
v_a_847_ = v___x_859_;
goto _start;
}
else
{
lean_dec(v_fst_851_);
v_a_846_ = v_tail_850_;
goto _start;
}
}
else
{
lean_dec(v_fst_851_);
v_a_846_ = v_tail_850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0(lean_object* v_f_863_, lean_object* v_x1_864_, lean_object* v_x2_865_, lean_object* v_x3_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_apply_3(v_f_863_, v_x1_864_, v_x2_865_, v_x3_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(lean_object* v_f_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_i_871_, lean_object* v_acc_872_){
_start:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_array_get_size(v_keys_869_);
v___x_874_ = lean_nat_dec_lt(v_i_871_, v___x_873_);
if (v___x_874_ == 0)
{
lean_dec(v_i_871_);
lean_dec(v_f_868_);
return v_acc_872_;
}
else
{
lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_k_875_ = lean_array_fget_borrowed(v_keys_869_, v_i_871_);
v_v_876_ = lean_array_fget_borrowed(v_vals_870_, v_i_871_);
lean_inc(v_f_868_);
lean_inc(v_v_876_);
lean_inc(v_k_875_);
v___x_877_ = lean_apply_3(v_f_868_, v_acc_872_, v_k_875_, v_v_876_);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_i_871_, v___x_878_);
lean_dec(v_i_871_);
v_i_871_ = v___x_879_;
v_acc_872_ = v___x_877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg___boxed(lean_object* v_f_881_, lean_object* v_keys_882_, lean_object* v_vals_883_, lean_object* v_i_884_, lean_object* v_acc_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_881_, v_keys_882_, v_vals_883_, v_i_884_, v_acc_885_);
lean_dec_ref(v_vals_883_);
lean_dec_ref(v_keys_882_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(lean_object* v_f_887_, lean_object* v_as_888_, size_t v_i_889_, size_t v_stop_890_, lean_object* v_b_891_){
_start:
{
lean_object* v___y_893_; uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_eq(v_i_889_, v_stop_890_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_array_uget_borrowed(v_as_888_, v_i_889_);
switch(lean_obj_tag(v___x_898_))
{
case 0:
{
lean_object* v_key_899_; lean_object* v_val_900_; lean_object* v___x_901_; 
v_key_899_ = lean_ctor_get(v___x_898_, 0);
v_val_900_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_f_887_);
lean_inc(v_val_900_);
lean_inc(v_key_899_);
v___x_901_ = lean_apply_3(v_f_887_, v_b_891_, v_key_899_, v_val_900_);
v___y_893_ = v___x_901_;
goto v___jp_892_;
}
case 1:
{
lean_object* v_node_902_; lean_object* v___x_903_; 
v_node_902_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_f_887_);
v___x_903_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_887_, v_node_902_, v_b_891_);
v___y_893_ = v___x_903_;
goto v___jp_892_;
}
default: 
{
v___y_893_ = v_b_891_;
goto v___jp_892_;
}
}
}
else
{
lean_dec(v_f_887_);
return v_b_891_;
}
v___jp_892_:
{
size_t v___x_894_; size_t v___x_895_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_889_, v___x_894_);
v_i_889_ = v___x_895_;
v_b_891_ = v___y_893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(lean_object* v_f_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v_es_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_es_907_ = lean_ctor_get(v_x_905_, 0);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_array_get_size(v_es_907_);
v___x_910_ = lean_nat_dec_lt(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec(v_f_904_);
return v_x_906_;
}
else
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_909_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_904_, v_es_907_, v___x_911_, v___x_912_, v_x_906_);
return v___x_913_;
}
}
else
{
lean_object* v_ks_914_; lean_object* v_vs_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_ks_914_ = lean_ctor_get(v_x_905_, 0);
v_vs_915_ = lean_ctor_get(v_x_905_, 1);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_904_, v_ks_914_, v_vs_915_, v___x_916_, v_x_906_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg___boxed(lean_object* v_f_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_918_, v_x_919_, v_x_920_);
lean_dec_ref(v_x_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg___boxed(lean_object* v_f_922_, lean_object* v_as_923_, lean_object* v_i_924_, lean_object* v_stop_925_, lean_object* v_b_926_){
_start:
{
size_t v_i_boxed_927_; size_t v_stop_boxed_928_; lean_object* v_res_929_; 
v_i_boxed_927_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_stop_boxed_928_ = lean_unbox_usize(v_stop_925_);
lean_dec(v_stop_925_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_922_, v_as_923_, v_i_boxed_927_, v_stop_boxed_928_, v_b_926_);
lean_dec_ref(v_as_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(lean_object* v_map_930_, lean_object* v_f_931_, lean_object* v_init_932_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; 
v___f_933_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___lam__0), 4, 1);
lean_closure_set(v___f_933_, 0, v_f_931_);
v___x_934_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v___f_933_, v_map_930_, v_init_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg___boxed(lean_object* v_map_935_, lean_object* v_f_936_, lean_object* v_init_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_map_935_, v_f_936_, v_init_937_);
lean_dec_ref(v_map_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___lam__0(lean_object* v_ps_939_, lean_object* v_k_940_, lean_object* v_v_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_k_940_);
lean_ctor_set(v___x_942_, 1, v_v_941_);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v_ps_939_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(lean_object* v_m_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___f_946_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___closed__0));
v___x_947_ = lean_box(0);
v___x_948_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_m_945_, v___f_946_, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg___boxed(lean_object* v_m_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v_m_949_);
lean_dec_ref(v_m_949_);
return v_res_950_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__0));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__2));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_box(1);
v___x_958_ = l_Lean_MessageData_ofFormat(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__5));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__9));
v___x_967_ = l_Lean_MessageData_ofFormat(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__12));
v___x_972_ = l_Lean_MessageData_ofFormat(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__14);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(lean_object* v_kind_977_, lean_object* v_a_978_, uint8_t v___x_979_, lean_object* v_diag_980_, lean_object* v___x_981_, uint8_t v_a_982_, uint8_t v_val_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; uint16_t v___y_1011_; lean_object* v___y_1012_; lean_object* v_fileName_1013_; lean_object* v_fileMap_1014_; lean_object* v_currNamespace_1015_; lean_object* v_openDecls_1016_; lean_object* v_initHeartbeats_1017_; lean_object* v_maxHeartbeats_1018_; lean_object* v_quotContext_1019_; lean_object* v_currMacroScope_1020_; lean_object* v_cancelTk_x3f_1021_; lean_object* v_inheritedTraceOptions_1022_; lean_object* v_currRecDepth_1023_; lean_object* v_ref_1024_; uint8_t v_suppressElabErrors_1025_; uint8_t v_checkDeprecated_1026_; uint8_t v_isRecordingDeps_1027_; lean_object* v___y_1028_; lean_object* v_toCold_1110_; lean_object* v_currRecDepth_1111_; lean_object* v_ref_1112_; uint8_t v_suppressElabErrors_1113_; uint8_t v_checkDeprecated_1114_; uint8_t v_isRecordingDeps_1115_; lean_object* v_fileName_1116_; lean_object* v_fileMap_1117_; lean_object* v_options_1118_; lean_object* v_currNamespace_1119_; lean_object* v_openDecls_1120_; lean_object* v_initHeartbeats_1121_; lean_object* v_maxHeartbeats_1122_; lean_object* v_quotContext_1123_; lean_object* v_currMacroScope_1124_; lean_object* v_cancelTk_x3f_1125_; lean_object* v_inheritedTraceOptions_1126_; uint16_t v___y_1128_; lean_object* v___y_1129_; uint8_t v___y_1130_; uint16_t v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; uint8_t v___y_1156_; uint16_t v___y_1158_; uint8_t v___y_1159_; lean_object* v___y_1160_; uint8_t v___y_1161_; lean_object* v___y_1163_; 
v_toCold_1110_ = lean_ctor_get(v___y_986_, 0);
v_currRecDepth_1111_ = lean_ctor_get(v___y_986_, 1);
v_ref_1112_ = lean_ctor_get(v___y_986_, 2);
v_suppressElabErrors_1113_ = lean_ctor_get_uint8(v___y_986_, sizeof(void*)*3 + 2);
v_checkDeprecated_1114_ = lean_ctor_get_uint8(v___y_986_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1115_ = lean_ctor_get_uint8(v___y_986_, sizeof(void*)*3 + 4);
v_fileName_1116_ = lean_ctor_get(v_toCold_1110_, 0);
v_fileMap_1117_ = lean_ctor_get(v_toCold_1110_, 1);
v_options_1118_ = lean_ctor_get(v_toCold_1110_, 2);
v_currNamespace_1119_ = lean_ctor_get(v_toCold_1110_, 4);
v_openDecls_1120_ = lean_ctor_get(v_toCold_1110_, 5);
v_initHeartbeats_1121_ = lean_ctor_get(v_toCold_1110_, 6);
v_maxHeartbeats_1122_ = lean_ctor_get(v_toCold_1110_, 7);
v_quotContext_1123_ = lean_ctor_get(v_toCold_1110_, 8);
v_currMacroScope_1124_ = lean_ctor_get(v_toCold_1110_, 9);
v_cancelTk_x3f_1125_ = lean_ctor_get(v_toCold_1110_, 10);
v_inheritedTraceOptions_1126_ = lean_ctor_get(v_toCold_1110_, 11);
if (v_isRecordingDeps_1115_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1118_);
v___x_1173_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_options_1118_, v___x_1172_, v_a_982_);
v___y_1163_ = v___x_1173_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1174_; 
lean_inc_ref(v_options_1118_);
v___x_1174_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_1118_);
v___y_1163_ = v___x_1174_;
goto v___jp_1162_;
}
v___jp_989_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_993_ = l_Lean_stringToMessageData(v_kind_977_);
v___x_994_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__1);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_inc_ref(v___y_992_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___y_992_);
v___x_997_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__3);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__4);
v___x_1000_ = l_Lean_MessageData_joinSep(v___y_991_, v___x_999_);
v___x_1001_ = l_Lean_indentD(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__6);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_Exception_toMessageData(v___y_990_);
v___x_1006_ = l_Lean_indentD(v___x_1005_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1004_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
v___jp_1010_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1029_ = l_Lean_maxRecDepth;
v___x_1030_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v___y_1012_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1031_, 0, v_fileName_1013_);
lean_ctor_set(v___x_1031_, 1, v_fileMap_1014_);
lean_ctor_set(v___x_1031_, 2, v___y_1012_);
lean_ctor_set(v___x_1031_, 3, v___x_1030_);
lean_ctor_set(v___x_1031_, 4, v_currNamespace_1015_);
lean_ctor_set(v___x_1031_, 5, v_openDecls_1016_);
lean_ctor_set(v___x_1031_, 6, v_initHeartbeats_1017_);
lean_ctor_set(v___x_1031_, 7, v_maxHeartbeats_1018_);
lean_ctor_set(v___x_1031_, 8, v_quotContext_1019_);
lean_ctor_set(v___x_1031_, 9, v_currMacroScope_1020_);
lean_ctor_set(v___x_1031_, 10, v_cancelTk_x3f_1021_);
lean_ctor_set(v___x_1031_, 11, v_inheritedTraceOptions_1022_);
lean_inc(v_ref_1024_);
lean_inc(v_currRecDepth_1023_);
v___x_1032_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v_currRecDepth_1023_);
lean_ctor_set(v___x_1032_, 2, v_ref_1024_);
lean_ctor_set_uint16(v___x_1032_, sizeof(void*)*3, v___y_1011_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*3 + 2, v_suppressElabErrors_1025_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*3 + 3, v_checkDeprecated_1026_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*3 + 4, v_isRecordingDeps_1027_);
lean_inc_ref(v_a_978_);
v___x_1033_ = l_Lean_Meta_check(v_a_978_, v___x_979_, v___y_984_, v___y_985_, v___x_1032_, v___y_1028_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v_diag_1035_; lean_object* v_unfoldCounter_1036_; lean_object* v___x_1037_; lean_object* v_mctx_1038_; lean_object* v_cache_1039_; lean_object* v_zetaDeltaFVarIds_1040_; lean_object* v_postponed_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref_known(v___x_1033_, 1);
v___x_1034_ = lean_st_ref_get(v___y_985_);
v_diag_1035_ = lean_ctor_get(v___x_1034_, 4);
lean_inc_ref(v_diag_1035_);
lean_dec(v___x_1034_);
v_unfoldCounter_1036_ = lean_ctor_get(v_diag_1035_, 0);
lean_inc_ref(v_unfoldCounter_1036_);
lean_dec_ref(v_diag_1035_);
v___x_1037_ = lean_st_ref_take(v___y_985_);
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
lean_ctor_set(v___x_1043_, 4, v_diag_980_);
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
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_diag_980_);
v___x_1046_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_st_ref_put(v___y_985_, v___x_1046_);
v___x_1048_ = 5;
v___x_1049_ = l_Lean_Meta_check(v_a_978_, v___x_1048_, v___y_984_, v___y_985_, v___x_1032_, v___y_1028_);
lean_dec_ref_known(v___x_1032_, 3);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_unfoldCounter_1036_);
lean_dec_ref(v_kind_977_);
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
v___x_1065_ = lean_st_ref_get(v___y_985_);
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
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_981_);
v___x_1073_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_env_1070_, v___x_1071_, v___x_1072_);
v___x_1074_ = l_List_isEmpty___redArg(v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
lean_del_object(v___x_1061_);
v___x_1075_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7));
v___x_1076_ = lean_string_dec_eq(v_kind_977_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__10);
v___y_990_ = v_a_1059_;
v___y_991_ = v___x_1073_;
v___y_992_ = v___x_1077_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__13);
v___y_990_ = v_a_1059_;
v___y_991_ = v___x_1073_;
v___y_992_ = v___x_1078_;
goto v___jp_989_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec(v___x_1073_);
lean_dec(v_a_1059_);
lean_dec_ref(v_kind_977_);
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
lean_dec_ref(v_kind_977_);
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
lean_dec_ref(v_kind_977_);
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
lean_dec_ref(v_diag_980_);
lean_dec_ref(v_a_978_);
lean_dec_ref(v_kind_977_);
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
v___jp_1127_:
{
lean_object* v___x_1131_; lean_object* v_env_1132_; lean_object* v_nextMacroScope_1133_; lean_object* v_ngen_1134_; lean_object* v_auxDeclNGen_1135_; lean_object* v_traceState_1136_; lean_object* v_recordedDeps_1137_; lean_object* v_messages_1138_; lean_object* v_infoState_1139_; lean_object* v_snapshotTasks_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
v___x_1131_ = lean_st_ref_take(v___y_987_);
v_env_1132_ = lean_ctor_get(v___x_1131_, 0);
v_nextMacroScope_1133_ = lean_ctor_get(v___x_1131_, 1);
v_ngen_1134_ = lean_ctor_get(v___x_1131_, 2);
v_auxDeclNGen_1135_ = lean_ctor_get(v___x_1131_, 3);
v_traceState_1136_ = lean_ctor_get(v___x_1131_, 4);
v_recordedDeps_1137_ = lean_ctor_get(v___x_1131_, 6);
v_messages_1138_ = lean_ctor_get(v___x_1131_, 7);
v_infoState_1139_ = lean_ctor_get(v___x_1131_, 8);
v_snapshotTasks_1140_ = lean_ctor_get(v___x_1131_, 9);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v___x_1131_, 5);
lean_dec(v_unused_1151_);
v___x_1142_ = v___x_1131_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snapshotTasks_1140_);
lean_inc(v_infoState_1139_);
lean_inc(v_messages_1138_);
lean_inc(v_recordedDeps_1137_);
lean_inc(v_traceState_1136_);
lean_inc(v_auxDeclNGen_1135_);
lean_inc(v_ngen_1134_);
lean_inc(v_nextMacroScope_1133_);
lean_inc(v_env_1132_);
lean_dec(v___x_1131_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = l_Lean_Kernel_enableDiag(v_env_1132_, v___y_1130_);
v___x_1145_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__15);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 5, v___x_1145_);
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_nextMacroScope_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_ngen_1134_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_auxDeclNGen_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_traceState_1136_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1149_, 6, v_recordedDeps_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_messages_1138_);
lean_ctor_set(v_reuseFailAlloc_1149_, 8, v_infoState_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 9, v_snapshotTasks_1140_);
v___x_1147_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_st_ref_put(v___y_987_, v___x_1147_);
lean_inc_ref(v_inheritedTraceOptions_1126_);
lean_inc(v_cancelTk_x3f_1125_);
lean_inc(v_currMacroScope_1124_);
lean_inc(v_quotContext_1123_);
lean_inc(v_maxHeartbeats_1122_);
lean_inc(v_initHeartbeats_1121_);
lean_inc(v_openDecls_1120_);
lean_inc(v_currNamespace_1119_);
lean_inc_ref(v_fileMap_1117_);
lean_inc_ref(v_fileName_1116_);
v___y_1011_ = v___y_1128_;
v___y_1012_ = v___y_1129_;
v_fileName_1013_ = v_fileName_1116_;
v_fileMap_1014_ = v_fileMap_1117_;
v_currNamespace_1015_ = v_currNamespace_1119_;
v_openDecls_1016_ = v_openDecls_1120_;
v_initHeartbeats_1017_ = v_initHeartbeats_1121_;
v_maxHeartbeats_1018_ = v_maxHeartbeats_1122_;
v_quotContext_1019_ = v_quotContext_1123_;
v_currMacroScope_1020_ = v_currMacroScope_1124_;
v_cancelTk_x3f_1021_ = v_cancelTk_x3f_1125_;
v_inheritedTraceOptions_1022_ = v_inheritedTraceOptions_1126_;
v_currRecDepth_1023_ = v_currRecDepth_1111_;
v_ref_1024_ = v_ref_1112_;
v_suppressElabErrors_1025_ = v_suppressElabErrors_1113_;
v_checkDeprecated_1026_ = v_checkDeprecated_1114_;
v_isRecordingDeps_1027_ = v_isRecordingDeps_1115_;
v___y_1028_ = v___y_987_;
goto v___jp_1010_;
}
}
}
v___jp_1152_:
{
if (v___y_1156_ == 0)
{
v___y_1128_ = v___y_1153_;
v___y_1129_ = v___y_1154_;
v___y_1130_ = v___y_1155_;
goto v___jp_1127_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_1126_);
lean_inc(v_cancelTk_x3f_1125_);
lean_inc(v_currMacroScope_1124_);
lean_inc(v_quotContext_1123_);
lean_inc(v_maxHeartbeats_1122_);
lean_inc(v_initHeartbeats_1121_);
lean_inc(v_openDecls_1120_);
lean_inc(v_currNamespace_1119_);
lean_inc_ref(v_fileMap_1117_);
lean_inc_ref(v_fileName_1116_);
v___y_1011_ = v___y_1153_;
v___y_1012_ = v___y_1154_;
v_fileName_1013_ = v_fileName_1116_;
v_fileMap_1014_ = v_fileMap_1117_;
v_currNamespace_1015_ = v_currNamespace_1119_;
v_openDecls_1016_ = v_openDecls_1120_;
v_initHeartbeats_1017_ = v_initHeartbeats_1121_;
v_maxHeartbeats_1018_ = v_maxHeartbeats_1122_;
v_quotContext_1019_ = v_quotContext_1123_;
v_currMacroScope_1020_ = v_currMacroScope_1124_;
v_cancelTk_x3f_1021_ = v_cancelTk_x3f_1125_;
v_inheritedTraceOptions_1022_ = v_inheritedTraceOptions_1126_;
v_currRecDepth_1023_ = v_currRecDepth_1111_;
v_ref_1024_ = v_ref_1112_;
v_suppressElabErrors_1025_ = v_suppressElabErrors_1113_;
v_checkDeprecated_1026_ = v_checkDeprecated_1114_;
v_isRecordingDeps_1027_ = v_isRecordingDeps_1115_;
v___y_1028_ = v___y_987_;
goto v___jp_1010_;
}
}
v___jp_1157_:
{
if (v___y_1161_ == 0)
{
if (v___y_1159_ == 0)
{
v___y_1153_ = v___y_1158_;
v___y_1154_ = v___y_1160_;
v___y_1155_ = v___y_1161_;
v___y_1156_ = v_a_982_;
goto v___jp_1152_;
}
else
{
v___y_1128_ = v___y_1158_;
v___y_1129_ = v___y_1160_;
v___y_1130_ = v___y_1161_;
goto v___jp_1127_;
}
}
else
{
v___y_1153_ = v___y_1158_;
v___y_1154_ = v___y_1160_;
v___y_1155_ = v___y_1161_;
v___y_1156_ = v___y_1159_;
goto v___jp_1152_;
}
}
v___jp_1162_:
{
uint16_t v___x_1164_; lean_object* v___x_1165_; lean_object* v_env_1166_; uint8_t v___x_1167_; uint16_t v___x_1168_; uint16_t v___x_1169_; uint16_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1164_ = l_Lean_OptionFlags_ofOptions(v___y_1163_);
v___x_1165_ = lean_st_ref_get(v___y_987_);
v_env_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_ref(v_env_1166_);
lean_dec(v___x_1165_);
v___x_1167_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1166_);
lean_dec_ref(v_env_1166_);
v___x_1168_ = 512;
v___x_1169_ = lean_uint16_land(v___x_1164_, v___x_1168_);
v___x_1170_ = 0;
v___x_1171_ = lean_uint16_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
v___y_1158_ = v___x_1164_;
v___y_1159_ = v___x_1167_;
v___y_1160_ = v___y_1163_;
v___y_1161_ = v_a_982_;
goto v___jp_1157_;
}
else
{
v___y_1158_ = v___x_1164_;
v___y_1159_ = v___x_1167_;
v___y_1160_ = v___y_1163_;
v___y_1161_ = v_val_983_;
goto v___jp_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed(lean_object* v_kind_1175_, lean_object* v_a_1176_, lean_object* v___x_1177_, lean_object* v_diag_1178_, lean_object* v___x_1179_, lean_object* v_a_1180_, lean_object* v_val_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v___x_27019__boxed_1187_; uint8_t v_a_27021__boxed_1188_; uint8_t v_val_27022__boxed_1189_; lean_object* v_res_1190_; 
v___x_27019__boxed_1187_ = lean_unbox(v___x_1177_);
v_a_27021__boxed_1188_ = lean_unbox(v_a_1180_);
v_val_27022__boxed_1189_ = lean_unbox(v_val_1181_);
v_res_1190_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0(v_kind_1175_, v_a_1176_, v___x_27019__boxed_1187_, v_diag_1178_, v___x_1179_, v_a_27021__boxed_1188_, v_val_27022__boxed_1189_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___x_1179_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object* v_kind_1196_, uint8_t v_a_1197_, uint8_t v_val_1198_, lean_object* v_as_x27_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
if (lean_obj_tag(v_as_x27_1199_) == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref(v_kind_1196_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_b_1200_);
return v___x_1206_;
}
else
{
lean_object* v_head_1207_; lean_object* v_tail_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_mctx_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_b_1200_);
v_head_1207_ = lean_ctor_get(v_as_x27_1199_, 0);
v_tail_1208_ = lean_ctor_get(v_as_x27_1199_, 1);
v___x_1209_ = lean_box(0);
v___x_1210_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0));
v___x_1211_ = lean_st_ref_get(v___y_1202_);
v_mctx_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_mctx_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1212_, v_head_1207_);
lean_dec_ref(v_mctx_1212_);
if (lean_obj_tag(v___x_1213_) == 1)
{
lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1267_; 
v_val_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1267_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1267_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_lctx_1218_; lean_object* v_type_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v_diag_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; 
v_lctx_1218_ = lean_ctor_get(v_val_1214_, 1);
lean_inc_ref(v_lctx_1218_);
v_type_1219_ = lean_ctor_get(v_val_1214_, 2);
lean_inc_ref(v_type_1219_);
lean_dec(v_val_1214_);
v___x_1220_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_1219_, v___y_1202_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_st_ref_get(v___y_1202_);
v_diag_1223_ = lean_ctor_get(v___x_1222_, 4);
lean_inc_ref_n(v_diag_1223_, 2);
lean_dec(v___x_1222_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__1));
v___x_1226_ = 1;
v___x_1227_ = lean_box(v___x_1226_);
v___x_1228_ = lean_box(v_a_1197_);
v___x_1229_ = lean_box(v_val_1198_);
lean_inc_ref(v_kind_1196_);
v___f_1230_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1230_, 0, v_kind_1196_);
lean_closure_set(v___f_1230_, 1, v_a_1221_);
lean_closure_set(v___f_1230_, 2, v___x_1227_);
lean_closure_set(v___f_1230_, 3, v_diag_1223_);
lean_closure_set(v___f_1230_, 4, v___x_1224_);
lean_closure_set(v___f_1230_, 5, v___x_1228_);
lean_closure_set(v___f_1230_, 6, v___x_1229_);
v___x_1231_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7___redArg(v_lctx_1218_, v___x_1225_, v___f_1230_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1258_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1258_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1258_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v_mctx_1237_; lean_object* v_cache_1238_; lean_object* v_zetaDeltaFVarIds_1239_; lean_object* v_postponed_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1256_; 
v___x_1236_ = lean_st_ref_take(v___y_1202_);
v_mctx_1237_ = lean_ctor_get(v___x_1236_, 0);
v_cache_1238_ = lean_ctor_get(v___x_1236_, 1);
v_zetaDeltaFVarIds_1239_ = lean_ctor_get(v___x_1236_, 2);
v_postponed_1240_ = lean_ctor_get(v___x_1236_, 3);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1236_, 4);
lean_dec(v_unused_1257_);
v___x_1242_ = v___x_1236_;
v_isShared_1243_ = v_isSharedCheck_1256_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_postponed_1240_);
lean_inc(v_zetaDeltaFVarIds_1239_);
lean_inc(v_cache_1238_);
lean_inc(v_mctx_1237_);
lean_dec(v___x_1236_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1256_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_diag_1223_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_mctx_1237_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_cache_1238_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_zetaDeltaFVarIds_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_postponed_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 4, v_diag_1223_);
v___x_1245_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_st_ref_put(v___y_1202_, v___x_1245_);
if (lean_obj_tag(v_a_1232_) == 1)
{
lean_object* v___x_1248_; 
lean_dec_ref(v_kind_1196_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_a_1232_);
v___x_1248_ = v___x_1216_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1232_);
v___x_1248_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1209_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1249_);
v___x_1251_ = v___x_1234_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
else
{
lean_del_object(v___x_1234_);
lean_dec(v_a_1232_);
lean_del_object(v___x_1216_);
v_as_x27_1199_ = v_tail_1208_;
v_b_1200_ = v___x_1210_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_diag_1223_);
lean_del_object(v___x_1216_);
lean_dec_ref(v_kind_1196_);
v_a_1259_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1231_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1231_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
else
{
lean_dec(v___x_1213_);
v_as_x27_1199_ = v_tail_1208_;
v_b_1200_ = v___x_1210_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object* v_kind_1269_, lean_object* v_a_1270_, lean_object* v_val_1271_, lean_object* v_as_x27_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_a_27356__boxed_1279_; uint8_t v_val_27357__boxed_1280_; lean_object* v_res_1281_; 
v_a_27356__boxed_1279_ = lean_unbox(v_a_1270_);
v_val_27357__boxed_1280_ = lean_unbox(v_val_1271_);
v_res_1281_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1269_, v_a_27356__boxed_1279_, v_val_27357__boxed_1280_, v_as_x27_1272_, v_b_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v_as_x27_1272_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(uint8_t v_a_1282_, uint8_t v_val_1283_, lean_object* v_kind_1284_, lean_object* v_goals_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___closed__0));
v___x_1293_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1284_, v_a_1282_, v_val_1283_, v_goals_1285_, v___x_1292_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1306_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1306_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1306_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_fst_1298_; 
v_fst_1298_ = lean_ctor_get(v_a_1294_, 0);
lean_inc(v_fst_1298_);
lean_dec(v_a_1294_);
if (lean_obj_tag(v_fst_1298_) == 0)
{
lean_object* v___x_1300_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1291_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1291_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
v_val_1302_ = lean_ctor_get(v_fst_1298_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v_fst_1298_, 1);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_val_1302_);
v___x_1304_ = v___x_1296_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_val_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1293_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1293_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed(lean_object* v_a_1315_, lean_object* v_val_1316_, lean_object* v_kind_1317_, lean_object* v_goals_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v_a_27497__boxed_1324_; uint8_t v_val_27498__boxed_1325_; lean_object* v_res_1326_; 
v_a_27497__boxed_1324_ = lean_unbox(v_a_1315_);
v_val_27498__boxed_1325_ = lean_unbox(v_val_1316_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1(v_a_27497__boxed_1324_, v_val_27498__boxed_1325_, v_kind_1317_, v_goals_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v_goals_1318_);
return v_res_1326_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1329_ = lean_box(1);
v___x_1330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_1331_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__0);
v___x_1332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1330_);
lean_ctor_set(v___x_1332_, 2, v___x_1329_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(lean_object* v_val_1334_, uint8_t v_a_1335_, lean_object* v___x_1336_, lean_object* v_ci_1337_, lean_object* v_info_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_a_1344_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = lean_st_ref_get(v_val_1334_);
v___x_1352_ = lean_unbox(v___x_1351_);
if (v___x_1352_ == 0)
{
if (lean_obj_tag(v_info_1338_) == 0)
{
lean_object* v_toCommandContextInfo_1353_; lean_object* v_i_1354_; lean_object* v_parentDecl_x3f_1355_; lean_object* v_autoImplicits_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1414_; 
v_toCommandContextInfo_1353_ = lean_ctor_get(v_ci_1337_, 0);
lean_inc_ref(v_toCommandContextInfo_1353_);
v_i_1354_ = lean_ctor_get(v_info_1338_, 0);
lean_inc_ref(v_i_1354_);
lean_dec_ref_known(v_info_1338_, 1);
v_parentDecl_x3f_1355_ = lean_ctor_get(v_ci_1337_, 1);
v_autoImplicits_1356_ = lean_ctor_get(v_ci_1337_, 2);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_ci_1337_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_ci_1337_, 0);
lean_dec(v_unused_1415_);
v___x_1358_ = v_ci_1337_;
v_isShared_1359_ = v_isSharedCheck_1414_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_autoImplicits_1356_);
lean_inc(v_parentDecl_x3f_1355_);
lean_dec(v_ci_1337_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1414_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_env_1360_; lean_object* v_cmdEnv_x3f_1361_; lean_object* v_fileMap_1362_; lean_object* v_options_1363_; lean_object* v_currNamespace_1364_; lean_object* v_openDecls_1365_; lean_object* v_ngen_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1412_; 
v_env_1360_ = lean_ctor_get(v_toCommandContextInfo_1353_, 0);
v_cmdEnv_x3f_1361_ = lean_ctor_get(v_toCommandContextInfo_1353_, 1);
v_fileMap_1362_ = lean_ctor_get(v_toCommandContextInfo_1353_, 2);
v_options_1363_ = lean_ctor_get(v_toCommandContextInfo_1353_, 4);
v_currNamespace_1364_ = lean_ctor_get(v_toCommandContextInfo_1353_, 5);
v_openDecls_1365_ = lean_ctor_get(v_toCommandContextInfo_1353_, 6);
v_ngen_1366_ = lean_ctor_get(v_toCommandContextInfo_1353_, 7);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_toCommandContextInfo_1353_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_toCommandContextInfo_1353_, 3);
lean_dec(v_unused_1413_);
v___x_1368_ = v_toCommandContextInfo_1353_;
v_isShared_1369_ = v_isSharedCheck_1412_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_ngen_1366_);
lean_inc(v_openDecls_1365_);
lean_inc(v_currNamespace_1364_);
lean_inc(v_options_1363_);
lean_inc(v_fileMap_1362_);
lean_inc(v_cmdEnv_x3f_1361_);
lean_inc(v_env_1360_);
lean_dec(v_toCommandContextInfo_1353_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1412_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_toElabInfo_1370_; lean_object* v_mctxBefore_1371_; lean_object* v_goalsBefore_1372_; lean_object* v_mctxAfter_1373_; lean_object* v_goalsAfter_1374_; lean_object* v_val_1376_; lean_object* v___x_1382_; 
v_toElabInfo_1370_ = lean_ctor_get(v_i_1354_, 0);
lean_inc_ref(v_toElabInfo_1370_);
v_mctxBefore_1371_ = lean_ctor_get(v_i_1354_, 1);
lean_inc_ref(v_mctxBefore_1371_);
v_goalsBefore_1372_ = lean_ctor_get(v_i_1354_, 2);
lean_inc(v_goalsBefore_1372_);
v_mctxAfter_1373_ = lean_ctor_get(v_i_1354_, 3);
lean_inc_ref(v_mctxAfter_1373_);
v_goalsAfter_1374_ = lean_ctor_get(v_i_1354_, 4);
lean_inc(v_goalsAfter_1374_);
lean_dec_ref(v_i_1354_);
lean_inc_ref(v_ngen_1366_);
lean_inc(v_openDecls_1365_);
lean_inc(v_currNamespace_1364_);
lean_inc_ref(v_options_1363_);
lean_inc_ref(v_fileMap_1362_);
lean_inc(v_cmdEnv_x3f_1361_);
lean_inc_ref(v_env_1360_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 3, v_mctxBefore_1371_);
v___x_1382_ = v___x_1368_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_env_1360_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_cmdEnv_x3f_1361_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_fileMap_1362_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_mctxBefore_1371_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_options_1363_);
lean_ctor_set(v_reuseFailAlloc_1411_, 5, v_currNamespace_1364_);
lean_ctor_set(v_reuseFailAlloc_1411_, 6, v_openDecls_1365_);
lean_ctor_set(v_reuseFailAlloc_1411_, 7, v_ngen_1366_);
v___x_1382_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1381_;
}
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_stx_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_box(v_a_1335_);
v___x_1378_ = lean_st_ref_swap(v_val_1334_, v___x_1377_);
lean_dec(v___x_1378_);
v_stx_1379_ = lean_ctor_get(v_toElabInfo_1370_, 1);
lean_inc(v_stx_1379_);
lean_dec_ref(v_toElabInfo_1370_);
v___x_1380_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v___x_1336_, v_stx_1379_, v_val_1376_, v___y_1340_, v___y_1341_);
return v___x_1380_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
lean_inc_ref(v_autoImplicits_1356_);
lean_inc(v_parentDecl_x3f_1355_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1382_);
v___x_1384_ = v___x_1358_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_parentDecl_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_autoImplicits_1356_);
v___x_1384_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1385_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1385_, 0, v_env_1360_);
lean_ctor_set(v___x_1385_, 1, v_cmdEnv_x3f_1361_);
lean_ctor_set(v___x_1385_, 2, v_fileMap_1362_);
lean_ctor_set(v___x_1385_, 3, v_mctxAfter_1373_);
lean_ctor_set(v___x_1385_, 4, v_options_1363_);
lean_ctor_set(v___x_1385_, 5, v_currNamespace_1364_);
lean_ctor_set(v___x_1385_, 6, v_openDecls_1365_);
lean_ctor_set(v___x_1385_, 7, v_ngen_1366_);
v___x_1386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_parentDecl_x3f_1355_);
lean_ctor_set(v___x_1386_, 2, v_autoImplicits_1356_);
v___x_1387_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__1);
v___x_1388_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___lam__0___closed__7));
v___x_1389_ = lean_box(v_a_1335_);
lean_inc(v___x_1351_);
v___x_1390_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed), 9, 4);
lean_closure_set(v___x_1390_, 0, v___x_1389_);
lean_closure_set(v___x_1390_, 1, v___x_1351_);
lean_closure_set(v___x_1390_, 2, v___x_1388_);
lean_closure_set(v___x_1390_, 3, v_goalsBefore_1372_);
v___x_1391_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_1384_, v___x_1387_, v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
if (lean_obj_tag(v_a_1392_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___closed__2));
v___x_1394_ = lean_box(v_a_1335_);
v___x_1395_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__1___boxed), 9, 4);
lean_closure_set(v___x_1395_, 0, v___x_1394_);
lean_closure_set(v___x_1395_, 1, v___x_1351_);
lean_closure_set(v___x_1395_, 2, v___x_1393_);
lean_closure_set(v___x_1395_, 3, v_goalsAfter_1374_);
v___x_1396_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_1386_, v___x_1387_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1406_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
if (lean_obj_tag(v_a_1397_) == 1)
{
lean_object* v_val_1401_; 
lean_del_object(v___x_1399_);
v_val_1401_ = lean_ctor_get(v_a_1397_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v_a_1397_, 1);
v_val_1376_ = v_val_1401_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec(v_a_1397_);
lean_dec_ref(v_toElabInfo_1370_);
lean_dec_ref(v___x_1336_);
v___x_1402_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; 
lean_dec_ref(v_toElabInfo_1370_);
lean_dec_ref(v___x_1336_);
v_a_1407_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1396_, 1);
v_a_1344_ = v_a_1407_;
goto v___jp_1343_;
}
}
else
{
lean_object* v_val_1408_; 
lean_dec_ref_known(v___x_1386_, 3);
lean_dec(v_goalsAfter_1374_);
lean_dec(v___x_1351_);
v_val_1408_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v_a_1392_, 1);
v_val_1376_ = v_val_1408_;
goto v___jp_1375_;
}
}
else
{
lean_object* v_a_1409_; 
lean_dec_ref_known(v___x_1386_, 3);
lean_dec(v_goalsAfter_1374_);
lean_dec_ref(v_toElabInfo_1370_);
lean_dec(v___x_1351_);
lean_dec_ref(v___x_1336_);
v_a_1409_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1391_, 1);
v_a_1344_ = v_a_1409_;
goto v___jp_1343_;
}
}
}
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v___x_1351_);
lean_dec_ref(v_info_1338_);
lean_dec_ref(v_ci_1337_);
lean_dec_ref(v___x_1336_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v___x_1351_);
lean_dec_ref(v_info_1338_);
lean_dec_ref(v_ci_1337_);
lean_dec_ref(v___x_1336_);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
v___jp_1343_:
{
lean_object* v_ref_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_ref_1345_ = lean_ctor_get(v___y_1340_, 7);
v___x_1346_ = lean_io_error_to_string(v_a_1344_);
v___x_1347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
v___x_1348_ = l_Lean_MessageData_ofFormat(v___x_1347_);
lean_inc(v_ref_1345_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_ref_1345_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed(lean_object* v_val_1420_, lean_object* v_a_1421_, lean_object* v___x_1422_, lean_object* v_ci_1423_, lean_object* v_info_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v_a_27592__boxed_1429_; lean_object* v_res_1430_; 
v_a_27592__boxed_1429_ = lean_unbox(v_a_1421_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2(v_val_1420_, v_a_27592__boxed_1429_, v___x_1422_, v_ci_1423_, v_info_1424_, v_x_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v_x_1425_);
lean_dec(v_val_1420_);
return v_res_1430_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_instMonadEIO___redArg();
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(lean_object* v_msg_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_toApplicative_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1471_; 
v___x_1438_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__0);
v___x_1439_ = l_StateRefT_x27_instMonad___redArg(v___x_1438_);
v_toApplicative_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v___x_1439_, 1);
lean_dec(v_unused_1472_);
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1471_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_toApplicative_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1471_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_toFunctor_1444_; lean_object* v_toSeq_1445_; lean_object* v_toSeqLeft_1446_; lean_object* v_toSeqRight_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1469_; 
v_toFunctor_1444_ = lean_ctor_get(v_toApplicative_1440_, 0);
v_toSeq_1445_ = lean_ctor_get(v_toApplicative_1440_, 2);
v_toSeqLeft_1446_ = lean_ctor_get(v_toApplicative_1440_, 3);
v_toSeqRight_1447_ = lean_ctor_get(v_toApplicative_1440_, 4);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_toApplicative_1440_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v_toApplicative_1440_, 1);
lean_dec(v_unused_1470_);
v___x_1449_ = v_toApplicative_1440_;
v_isShared_1450_ = v_isSharedCheck_1469_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_toSeqRight_1447_);
lean_inc(v_toSeqLeft_1446_);
lean_inc(v_toSeq_1445_);
lean_inc(v_toFunctor_1444_);
lean_dec(v_toApplicative_1440_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1469_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___f_1451_; lean_object* v___f_1452_; lean_object* v___f_1453_; lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___f_1458_; lean_object* v___x_1460_; 
v___f_1451_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__1));
v___f_1452_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___closed__2));
lean_inc_ref(v_toFunctor_1444_);
v___f_1453_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1453_, 0, v_toFunctor_1444_);
v___f_1454_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1454_, 0, v_toFunctor_1444_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___f_1453_);
lean_ctor_set(v___x_1455_, 1, v___f_1454_);
v___f_1456_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1456_, 0, v_toSeqRight_1447_);
v___f_1457_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1457_, 0, v_toSeqLeft_1446_);
v___f_1458_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1458_, 0, v_toSeq_1445_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 4, v___f_1456_);
lean_ctor_set(v___x_1449_, 3, v___f_1457_);
lean_ctor_set(v___x_1449_, 2, v___f_1458_);
lean_ctor_set(v___x_1449_, 1, v___f_1451_);
lean_ctor_set(v___x_1449_, 0, v___x_1455_);
v___x_1460_ = v___x_1449_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___f_1451_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v___f_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v___f_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___f_1456_);
v___x_1460_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___f_1452_);
lean_ctor_set(v___x_1442_, 0, v___x_1460_);
v___x_1462_ = v___x_1442_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___f_1452_);
v___x_1462_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_22852__overap_1465_; lean_object* v___x_1466_; 
v___x_1463_ = lean_box(0);
v___x_1464_ = l_instInhabitedOfMonad___redArg(v___x_1462_, v___x_1463_);
v___x_22852__overap_1465_ = lean_panic_fn_borrowed(v___x_1464_, v_msg_1434_);
lean_dec(v___x_1464_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
v___x_1466_ = lean_apply_3(v___x_22852__overap_1465_, v___y_1435_, v___y_1436_, lean_box(0));
return v___x_1466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v_msg_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1477_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__2));
v___x_1482_ = lean_unsigned_to_nat(21u);
v___x_1483_ = lean_unsigned_to_nat(65u);
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__1));
v___x_1485_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__0));
v___x_1486_ = l_mkPanicMessageWithDecl(v___x_1485_, v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(lean_object* v_preNode_1487_, lean_object* v_postNode_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
switch(lean_obj_tag(v_x_1490_))
{
case 0:
{
lean_object* v_i_1494_; lean_object* v_t_1495_; lean_object* v___x_1496_; 
v_i_1494_ = lean_ctor_get(v_x_1490_, 0);
lean_inc_ref(v_i_1494_);
v_t_1495_ = lean_ctor_get(v_x_1490_, 1);
lean_inc_ref(v_t_1495_);
lean_dec_ref_known(v_x_1490_, 2);
v___x_1496_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1494_, v_x_1489_);
v_x_1489_ = v___x_1496_;
v_x_1490_ = v_t_1495_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1489_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref_known(v_x_1490_, 2);
lean_dec_ref(v_postNode_1488_);
lean_dec_ref(v_preNode_1487_);
v___x_1498_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___closed__3);
v___x_1499_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v___x_1498_, v___y_1491_, v___y_1492_);
return v___x_1499_;
}
else
{
lean_object* v_i_1500_; lean_object* v_children_1501_; lean_object* v_val_1502_; lean_object* v___x_1503_; 
v_i_1500_ = lean_ctor_get(v_x_1490_, 0);
lean_inc_ref_n(v_i_1500_, 2);
v_children_1501_ = lean_ctor_get(v_x_1490_, 1);
lean_inc_ref_n(v_children_1501_, 2);
lean_dec_ref_known(v_x_1490_, 2);
v_val_1502_ = lean_ctor_get(v_x_1489_, 0);
lean_inc_n(v_val_1502_, 2);
lean_inc_ref(v_preNode_1487_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
v___x_1503_ = lean_apply_6(v_preNode_1487_, v_val_1502_, v_i_1500_, v_children_1501_, v___y_1491_, v___y_1492_, lean_box(0));
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; uint8_t v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = lean_unbox(v_a_1504_);
lean_dec(v_a_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v_preNode_1487_);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1489_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_x_1489_, 0);
lean_dec(v_unused_1531_);
v___x_1507_ = v_x_1489_;
v_isShared_1508_ = v_isSharedCheck_1530_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_x_1489_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1530_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_box(0);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
v___x_1510_ = lean_apply_7(v_postNode_1488_, v_val_1502_, v_i_1500_, v_children_1501_, v___x_1509_, v___y_1491_, v___y_1492_, lean_box(0));
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1521_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1521_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1521_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_a_1511_);
v___x_1516_ = v___x_1507_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_1507_);
v_a_1522_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1510_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1510_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1489_, v_i_1500_);
v___x_1533_ = l_Lean_PersistentArray_toList___redArg(v_children_1501_);
v___x_1534_ = lean_box(0);
lean_inc_ref(v_postNode_1488_);
v___x_1535_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1487_, v_postNode_1488_, v___x_1532_, v___x_1533_, v___x_1534_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
v___x_1537_ = lean_apply_7(v_postNode_1488_, v_val_1502_, v_i_1500_, v_children_1501_, v_a_1536_, v___y_1491_, v___y_1492_, lean_box(0));
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_a_1547_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1537_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1537_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_val_1502_);
lean_dec_ref(v_children_1501_);
lean_dec_ref(v_i_1500_);
lean_dec_ref(v_postNode_1488_);
v_a_1555_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1535_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1535_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_val_1502_);
lean_dec_ref(v_children_1501_);
lean_dec_ref(v_i_1500_);
lean_dec_ref_known(v_x_1489_, 1);
lean_dec_ref(v_postNode_1488_);
lean_dec_ref(v_preNode_1487_);
v_a_1563_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1503_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1503_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
default: 
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_x_1489_);
lean_dec_ref(v_postNode_1488_);
lean_dec_ref(v_preNode_1487_);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_x_1490_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_x_1490_, 0);
lean_dec(v_unused_1579_);
v___x_1572_ = v_x_1490_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_x_1490_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(0);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(lean_object* v_preNode_1580_, lean_object* v_postNode_1581_, lean_object* v___x_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
if (lean_obj_tag(v_x_1583_) == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v___x_1582_);
lean_dec_ref(v_postNode_1581_);
lean_dec_ref(v_preNode_1580_);
v___x_1588_ = l_List_reverse___redArg(v_x_1584_);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
else
{
lean_object* v_head_1590_; lean_object* v_tail_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1609_; 
v_head_1590_ = lean_ctor_get(v_x_1583_, 0);
v_tail_1591_ = lean_ctor_get(v_x_1583_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1593_ = v_x_1583_;
v_isShared_1594_ = v_isSharedCheck_1609_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_tail_1591_);
lean_inc(v_head_1590_);
lean_dec(v_x_1583_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1609_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; 
lean_inc(v___x_1582_);
lean_inc_ref(v_postNode_1581_);
lean_inc_ref(v_preNode_1580_);
v___x_1595_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1580_, v_postNode_1581_, v___x_1582_, v_head_1590_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v_x_1584_);
lean_ctor_set(v___x_1593_, 0, v_a_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_x_1584_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
v_x_1583_ = v_tail_1591_;
v_x_1584_ = v___x_1598_;
goto _start;
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_del_object(v___x_1593_);
lean_dec(v_tail_1591_);
lean_dec(v_x_1584_);
lean_dec(v___x_1582_);
lean_dec_ref(v_postNode_1581_);
lean_dec_ref(v_preNode_1580_);
v_a_1601_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1595_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1595_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg___boxed(lean_object* v_preNode_1610_, lean_object* v_postNode_1611_, lean_object* v___x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1610_, v_postNode_1611_, v___x_1612_, v_x_1613_, v_x_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg___boxed(lean_object* v_preNode_1619_, lean_object* v_postNode_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1619_, v_postNode_1620_, v_x_1621_, v_x_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(lean_object* v_postNode_1627_, lean_object* v_ci_1628_, lean_object* v_i_1629_, lean_object* v_cs_1630_, lean_object* v_x_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
v___x_1635_ = lean_apply_6(v_postNode_1627_, v_ci_1628_, v_i_1629_, v_cs_1630_, v___y_1632_, v___y_1633_, lean_box(0));
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed(lean_object* v_postNode_1636_, lean_object* v_ci_1637_, lean_object* v_i_1638_, lean_object* v_cs_1639_, lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0(v_postNode_1636_, v_ci_1637_, v_i_1638_, v_cs_1639_, v_x_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v_x_1640_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object* v_preNode_1645_, lean_object* v_postNode_1646_, lean_object* v_ctx_x3f_1647_, lean_object* v_t_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1652_, 0, v_postNode_1646_);
v___x_1653_ = lean_box(0);
v___x_1654_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1645_, v___f_1652_, v_ctx_x3f_1647_, v_t_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1662_);
v___x_1656_ = v___x_1654_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v___x_1654_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1653_);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1653_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1654_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1654_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object* v_preNode_1671_, lean_object* v_postNode_1672_, lean_object* v_ctx_x3f_1673_, lean_object* v_t_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_preNode_1671_, v_postNode_1672_, v_ctx_x3f_1673_, v_t_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(uint8_t v_a_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_box(v_a_1679_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object* v_a_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v_a_28154__boxed_1695_; lean_object* v_res_1696_; 
v_a_28154__boxed_1695_ = lean_unbox(v_a_1688_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_a_28154__boxed_1695_, v_x_1689_, v_x_1690_, v_x_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec_ref(v_x_1691_);
lean_dec_ref(v_x_1690_);
lean_dec_ref(v_x_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(uint8_t v_a_1697_, lean_object* v_val_1698_, lean_object* v_as_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_dec(v_val_1698_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_b_1702_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1708_ = lean_box(v_a_1697_);
v___f_1709_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1709_, 0, v___x_1708_);
v___x_1710_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1711_ = lean_box(v_a_1697_);
lean_inc(v_val_1698_);
v___f_1712_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1712_, 0, v_val_1698_);
lean_closure_set(v___f_1712_, 1, v___x_1711_);
lean_closure_set(v___f_1712_, 2, v___x_1710_);
v___x_1713_ = lean_box(0);
v_a_1714_ = lean_array_uget_borrowed(v_as_1699_, v_i_1701_);
v___x_1715_ = lean_box(0);
lean_inc(v_a_1714_);
v___x_1716_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___f_1709_, v___f_1712_, v___x_1715_, v_a_1714_, v___y_1703_, v___y_1704_);
if (lean_obj_tag(v___x_1716_) == 0)
{
size_t v___x_1717_; size_t v___x_1718_; 
lean_dec_ref_known(v___x_1716_, 1);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1701_, v___x_1717_);
v_i_1701_ = v___x_1718_;
v_b_1702_ = v___x_1713_;
goto _start;
}
else
{
lean_dec(v_val_1698_);
return v___x_1716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object* v_a_1720_, lean_object* v_val_1721_, lean_object* v_as_1722_, lean_object* v_sz_1723_, lean_object* v_i_1724_, lean_object* v_b_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_a_28179__boxed_1729_; size_t v_sz_boxed_1730_; size_t v_i_boxed_1731_; lean_object* v_res_1732_; 
v_a_28179__boxed_1729_ = lean_unbox(v_a_1720_);
v_sz_boxed_1730_ = lean_unbox_usize(v_sz_1723_);
lean_dec(v_sz_1723_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_a_28179__boxed_1729_, v_val_1721_, v_as_1722_, v_sz_boxed_1730_, v_i_boxed_1731_, v_b_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v_as_1722_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object* v_opt_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_scopes_1738_; lean_object* v___x_1739_; lean_object* v_opts_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1736_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1737_ = lean_st_ref_get(v___y_1734_);
v_scopes_1738_ = lean_ctor_get(v___x_1737_, 2);
lean_inc(v_scopes_1738_);
lean_dec(v___x_1737_);
v___x_1739_ = l_List_head_x21___redArg(v___x_1736_, v_scopes_1738_);
lean_dec(v_scopes_1738_);
v_opts_1740_ = lean_ctor_get(v___x_1739_, 1);
lean_inc_ref(v_opts_1740_);
lean_dec(v___x_1739_);
v___x_1741_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0_spec__0(v_opts_1740_, v_opt_1733_);
lean_dec_ref(v_opts_1740_);
v___x_1742_ = lean_box(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object* v_opt_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v_opt_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object* v___cmdStx_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1783_; 
v___x_1752_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1753_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_1752_, v___y_1750_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1783_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1783_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_unbox(v_a_1754_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec(v_a_1754_);
v___x_1759_ = lean_box(0);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1759_);
v___x_1761_ = v___x_1756_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
else
{
lean_object* v___x_1763_; lean_object* v_infoState_1764_; lean_object* v_trees_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; size_t v_sz_1771_; size_t v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
lean_del_object(v___x_1756_);
v___x_1763_ = lean_st_ref_get(v___y_1750_);
v_infoState_1764_ = lean_ctor_get(v___x_1763_, 8);
lean_inc_ref(v_infoState_1764_);
lean_dec(v___x_1763_);
v_trees_1765_ = lean_ctor_get(v_infoState_1764_, 2);
lean_inc_ref(v_trees_1765_);
lean_dec_ref(v_infoState_1764_);
v___x_1766_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1765_);
lean_dec_ref(v_trees_1765_);
v___x_1767_ = 0;
v___x_1768_ = lean_box(v___x_1767_);
v___x_1769_ = lean_st_mk_ref(v___x_1768_);
v___x_1770_ = lean_box(0);
v_sz_1771_ = lean_array_size(v___x_1766_);
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = lean_unbox(v_a_1754_);
lean_dec(v_a_1754_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___x_1773_, v___x_1769_, v___x_1766_, v_sz_1771_, v___x_1772_, v___x_1770_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___x_1766_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1774_, 0);
lean_dec(v_unused_1782_);
v___x_1776_ = v___x_1774_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v___x_1774_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1770_);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1770_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object* v___cmdStx_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(v___cmdStx_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___cmdStx_1784_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object* v_opt_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1797_, v___y_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object* v_opt_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_opt_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object* v_00_u03b2_1807_, lean_object* v_m_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___redArg(v_m_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object* v_00_u03b2_1810_, lean_object* v_m_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_00_u03b2_1810_, v_m_1811_);
lean_dec_ref(v_m_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object* v_kind_1813_, uint8_t v_a_1814_, uint8_t v_val_1815_, lean_object* v_as_1816_, lean_object* v_as_x27_1817_, lean_object* v_b_1818_, lean_object* v_a_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_kind_1813_, v_a_1814_, v_val_1815_, v_as_x27_1817_, v_b_1818_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object* v_kind_1826_, lean_object* v_a_1827_, lean_object* v_val_1828_, lean_object* v_as_1829_, lean_object* v_as_x27_1830_, lean_object* v_b_1831_, lean_object* v_a_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v_a_28372__boxed_1838_; uint8_t v_val_28373__boxed_1839_; lean_object* v_res_1840_; 
v_a_28372__boxed_1838_ = lean_unbox(v_a_1827_);
v_val_28373__boxed_1839_ = lean_unbox(v_val_1828_);
v_res_1840_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_kind_1826_, v_a_28372__boxed_1838_, v_val_28373__boxed_1839_, v_as_1829_, v_as_x27_1830_, v_b_1831_, v_a_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v_as_x27_1830_);
lean_dec(v_as_1829_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(lean_object* v_00_u03b2_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___redArg(v_x_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4(v_00_u03b2_1845_, v_x_1846_, v_x_1847_);
lean_dec(v_x_1847_);
lean_dec_ref(v_x_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5(lean_object* v_00_u03b2_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5___redArg(v_x_1850_, v_x_1851_, v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(lean_object* v_00_u03c3_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_map_1856_, lean_object* v_init_1857_, lean_object* v_f_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___redArg(v_map_1856_, v_init_1857_, v_f_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1860_, lean_object* v_00_u03b2_1861_, lean_object* v_map_1862_, lean_object* v_init_1863_, lean_object* v_f_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6(v_00_u03c3_1860_, v_00_u03b2_1861_, v_map_1862_, v_init_1863_, v_f_1864_);
lean_dec_ref(v_map_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(lean_object* v_00_u03c3_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_map_1868_, lean_object* v_f_1869_, lean_object* v_init_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___redArg(v_map_1868_, v_f_1869_, v_init_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8___boxed(lean_object* v_00_u03c3_1872_, lean_object* v_00_u03b2_1873_, lean_object* v_map_1874_, lean_object* v_f_1875_, lean_object* v_init_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8(v_00_u03c3_1872_, v_00_u03b2_1873_, v_map_1874_, v_f_1875_, v_init_1876_);
lean_dec_ref(v_map_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(lean_object* v_00_u03b1_1878_, lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___redArg(v_msg_1879_, v___y_1880_, v___y_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b1_1884_, lean_object* v_msg_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__23(v_00_u03b1_1884_, v_msg_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(lean_object* v_00_u03b1_1890_, lean_object* v_preNode_1891_, lean_object* v_postNode_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___redArg(v_preNode_1891_, v_postNode_1892_, v_x_1893_, v_x_1894_, v___y_1895_, v___y_1896_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_preNode_1900_, lean_object* v_postNode_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17(v_00_u03b1_1899_, v_preNode_1900_, v_postNode_1901_, v_x_1902_, v_x_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, size_t v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___redArg(v_x_1909_, v_x_1910_, v_x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
size_t v_x_28447__boxed_1917_; lean_object* v_res_1918_; 
v_x_28447__boxed_1917_ = lean_unbox_usize(v_x_1915_);
lean_dec(v_x_1915_);
v_res_1918_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6(v_00_u03b2_1913_, v_x_1914_, v_x_28447__boxed_1917_, v_x_1916_);
lean_dec(v_x_1916_);
lean_dec_ref(v_x_1914_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, size_t v_x_1921_, size_t v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___redArg(v_x_1920_, v_x_1921_, v_x_1922_, v_x_1923_, v_x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
size_t v_x_28458__boxed_1932_; size_t v_x_28459__boxed_1933_; lean_object* v_res_1934_; 
v_x_28458__boxed_1932_ = lean_unbox_usize(v_x_1928_);
lean_dec(v_x_1928_);
v_x_28459__boxed_1933_ = lean_unbox_usize(v_x_1929_);
lean_dec(v_x_1929_);
v_res_1934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8(v_00_u03b2_1926_, v_x_1927_, v_x_28458__boxed_1932_, v_x_28459__boxed_1933_, v_x_1930_, v_x_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10___redArg(lean_object* v_map_1935_, lean_object* v_f_1936_, lean_object* v_init_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_1936_, v_map_1935_, v_init_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10(lean_object* v_00_u03c3_1939_, lean_object* v_00_u03c3_1940_, lean_object* v_00_u03b2_1941_, lean_object* v_map_1942_, lean_object* v_f_1943_, lean_object* v_init_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_1943_, v_map_1942_, v_init_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(lean_object* v_map_1946_, lean_object* v_f_1947_, lean_object* v_init_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_1947_, v_map_1946_, v_init_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_map_1950_, lean_object* v_f_1951_, lean_object* v_init_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___redArg(v_map_1950_, v_f_1951_, v_init_1952_);
lean_dec_ref(v_map_1950_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(lean_object* v_00_u03c3_1954_, lean_object* v_00_u03b2_1955_, lean_object* v_map_1956_, lean_object* v_f_1957_, lean_object* v_init_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_1957_, v_map_1956_, v_init_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03c3_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_map_1962_, lean_object* v_f_1963_, lean_object* v_init_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13(v_00_u03c3_1960_, v_00_u03b2_1961_, v_map_1962_, v_f_1963_, v_init_1964_);
lean_dec_ref(v_map_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(lean_object* v_msgData_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___redArg(v_msgData_1966_, v___y_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28___boxed(lean_object* v_msgData_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9_spec__15_spec__20_spec__28(v_msgData_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(lean_object* v_00_u03b1_1976_, lean_object* v_preNode_1977_, lean_object* v_postNode_1978_, lean_object* v___x_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___redArg(v_preNode_1977_, v_postNode_1978_, v___x_1979_, v_x_1980_, v_x_1981_, v___y_1982_, v___y_1983_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_preNode_1987_, lean_object* v_postNode_1988_, lean_object* v___x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__17_spec__24(v_00_u03b1_1986_, v_preNode_1987_, v_postNode_1988_, v___x_1989_, v_x_1990_, v_x_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1996_, lean_object* v_keys_1997_, lean_object* v_vals_1998_, lean_object* v_heq_1999_, lean_object* v_i_2000_, lean_object* v_k_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1997_, v_vals_1998_, v_i_2000_, v_k_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_2003_, lean_object* v_keys_2004_, lean_object* v_vals_2005_, lean_object* v_heq_2006_, lean_object* v_i_2007_, lean_object* v_k_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_2003_, v_keys_2004_, v_vals_2005_, v_heq_2006_, v_i_2007_, v_k_2008_);
lean_dec(v_k_2008_);
lean_dec_ref(v_vals_2005_);
lean_dec_ref(v_keys_2004_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18(lean_object* v_00_u03b2_2010_, lean_object* v_n_2011_, lean_object* v_k_2012_, lean_object* v_v_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18___redArg(v_n_2011_, v_k_2012_, v_v_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(lean_object* v_00_u03b2_2015_, size_t v_depth_2016_, lean_object* v_keys_2017_, lean_object* v_vals_2018_, lean_object* v_heq_2019_, lean_object* v_i_2020_, lean_object* v_entries_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___redArg(v_depth_2016_, v_keys_2017_, v_vals_2018_, v_i_2020_, v_entries_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19___boxed(lean_object* v_00_u03b2_2023_, lean_object* v_depth_2024_, lean_object* v_keys_2025_, lean_object* v_vals_2026_, lean_object* v_heq_2027_, lean_object* v_i_2028_, lean_object* v_entries_2029_){
_start:
{
size_t v_depth_boxed_2030_; lean_object* v_res_2031_; 
v_depth_boxed_2030_ = lean_unbox_usize(v_depth_2024_);
lean_dec(v_depth_2024_);
v_res_2031_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__19(v_00_u03b2_2023_, v_depth_boxed_2030_, v_keys_2025_, v_vals_2026_, v_heq_2027_, v_i_2028_, v_entries_2029_);
lean_dec_ref(v_vals_2026_);
lean_dec_ref(v_keys_2025_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22(lean_object* v_00_u03c3_2032_, lean_object* v_00_u03c3_2033_, lean_object* v_00_u03b1_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_f_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22___redArg(v_f_2036_, v_x_2037_, v_x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(lean_object* v_00_u03c3_2040_, lean_object* v_00_u03b1_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_f_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___redArg(v_f_2043_, v_x_2044_, v_x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25___boxed(lean_object* v_00_u03c3_2047_, lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_f_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25(v_00_u03c3_2047_, v_00_u03b1_2048_, v_00_u03b2_2049_, v_f_2050_, v_x_2051_, v_x_2052_);
lean_dec_ref(v_x_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24(lean_object* v_00_u03b2_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__5_spec__8_spec__18_spec__24___redArg(v_x_2055_, v_x_2056_, v_x_2057_, v_x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_00_u03c3_2062_, lean_object* v_00_u03c3_2063_, lean_object* v_f_2064_, lean_object* v_as_2065_, size_t v_i_2066_, size_t v_stop_2067_, lean_object* v_b_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___redArg(v_f_2064_, v_as_2065_, v_i_2066_, v_stop_2067_, v_b_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_00_u03c3_2072_, lean_object* v_00_u03c3_2073_, lean_object* v_f_2074_, lean_object* v_as_2075_, lean_object* v_i_2076_, lean_object* v_stop_2077_, lean_object* v_b_2078_){
_start:
{
size_t v_i_boxed_2079_; size_t v_stop_boxed_2080_; lean_object* v_res_2081_; 
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_stop_boxed_2080_ = lean_unbox_usize(v_stop_2077_);
lean_dec(v_stop_2077_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__28(v_00_u03b1_2070_, v_00_u03b2_2071_, v_00_u03c3_2072_, v_00_u03c3_2073_, v_f_2074_, v_as_2075_, v_i_boxed_2079_, v_stop_boxed_2080_, v_b_2078_);
lean_dec_ref(v_as_2075_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(lean_object* v_00_u03c3_2082_, lean_object* v_00_u03c3_2083_, lean_object* v_00_u03b1_2084_, lean_object* v_00_u03b2_2085_, lean_object* v_f_2086_, lean_object* v_keys_2087_, lean_object* v_vals_2088_, lean_object* v_heq_2089_, lean_object* v_i_2090_, lean_object* v_acc_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___redArg(v_f_2086_, v_keys_2087_, v_vals_2088_, v_i_2090_, v_acc_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29___boxed(lean_object* v_00_u03c3_2093_, lean_object* v_00_u03c3_2094_, lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_f_2097_, lean_object* v_keys_2098_, lean_object* v_vals_2099_, lean_object* v_heq_2100_, lean_object* v_i_2101_, lean_object* v_acc_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3_spec__6_spec__10_spec__22_spec__29(v_00_u03c3_2093_, v_00_u03c3_2094_, v_00_u03b1_2095_, v_00_u03b2_2096_, v_f_2097_, v_keys_2098_, v_vals_2099_, v_heq_2100_, v_i_2101_, v_acc_2102_);
lean_dec_ref(v_vals_2099_);
lean_dec_ref(v_keys_2098_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(lean_object* v_00_u03b1_2104_, lean_object* v_00_u03b2_2105_, lean_object* v_00_u03c3_2106_, lean_object* v_f_2107_, lean_object* v_as_2108_, size_t v_i_2109_, size_t v_stop_2110_, lean_object* v_b_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___redArg(v_f_2107_, v_as_2108_, v_i_2109_, v_stop_2110_, v_b_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_00_u03c3_2115_, lean_object* v_f_2116_, lean_object* v_as_2117_, lean_object* v_i_2118_, lean_object* v_stop_2119_, lean_object* v_b_2120_){
_start:
{
size_t v_i_boxed_2121_; size_t v_stop_boxed_2122_; lean_object* v_res_2123_; 
v_i_boxed_2121_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_stop_boxed_2122_ = lean_unbox_usize(v_stop_2119_);
lean_dec(v_stop_2119_);
v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__32(v_00_u03b1_2113_, v_00_u03b2_2114_, v_00_u03c3_2115_, v_f_2116_, v_as_2117_, v_i_boxed_2121_, v_stop_boxed_2122_, v_b_2120_);
lean_dec_ref(v_as_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(lean_object* v_00_u03c3_2124_, lean_object* v_00_u03b1_2125_, lean_object* v_00_u03b2_2126_, lean_object* v_f_2127_, lean_object* v_keys_2128_, lean_object* v_vals_2129_, lean_object* v_heq_2130_, lean_object* v_i_2131_, lean_object* v_acc_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___redArg(v_f_2127_, v_keys_2128_, v_vals_2129_, v_i_2131_, v_acc_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2134_, lean_object* v_00_u03b1_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_f_2137_, lean_object* v_keys_2138_, lean_object* v_vals_2139_, lean_object* v_heq_2140_, lean_object* v_i_2141_, lean_object* v_acc_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4_spec__8_spec__13_spec__25_spec__33(v_00_u03c3_2134_, v_00_u03b1_2135_, v_00_u03b2_2136_, v_f_2137_, v_keys_2138_, v_vals_2139_, v_heq_2140_, v_i_2141_, v_acc_2142_);
lean_dec_ref(v_vals_2139_);
lean_dec_ref(v_keys_2138_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances));
v___x_2146_ = l_Lean_Elab_Command_addLinter(v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
return v_res_2148_;
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
