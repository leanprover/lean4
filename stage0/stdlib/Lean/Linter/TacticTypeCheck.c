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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isInstanceCore(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "initial"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "produced"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0;
static lean_once_cell_t l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___boxed(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = " tactic goal is not type-correct at `.implicit` transparency; "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = " some of the following as `@[implicit_reducible]`:"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nFull error:"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "consider using propositional rewriting or marking"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "consider rephrasing the goal or marking"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = l_Lean_Expr_hasMVar(v_e_83_);
v___x_87_ = lean_bool_not(v___x_86_);
if (v___x_87_ == 0)
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
v___x_103_ = lean_st_ref_set(v___y_84_, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v_fst_91_);
return v___x_104_;
}
}
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v_e_83_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg___boxed(lean_object* v_e_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_109_, v___y_110_);
lean_dec(v___y_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(lean_object* v_e_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_e_113_, v___y_115_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___boxed(lean_object* v_e_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1(v_e_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
lean_object* v_name_129_; lean_object* v_defValue_130_; lean_object* v_map_131_; lean_object* v___x_132_; 
v_name_129_ = lean_ctor_get(v_opt_128_, 0);
v_defValue_130_ = lean_ctor_get(v_opt_128_, 1);
v_map_131_ = lean_ctor_get(v_opts_127_, 0);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_131_, v_name_129_);
if (lean_obj_tag(v___x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = lean_unbox(v_defValue_130_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_132_, 1);
if (lean_obj_tag(v_val_134_) == 1)
{
uint8_t v_v_135_; 
v_v_135_ = lean_ctor_get_uint8(v_val_134_, 0);
lean_dec_ref_known(v_val_134_, 0);
return v_v_135_;
}
else
{
uint8_t v___x_136_; 
lean_dec(v_val_134_);
v___x_136_ = lean_unbox(v_defValue_130_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_137_, v_opt_138_);
lean_dec_ref(v_opt_138_);
lean_dec_ref(v_opts_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object* v_opts_141_, lean_object* v_opt_142_){
_start:
{
lean_object* v_name_143_; lean_object* v_defValue_144_; lean_object* v_map_145_; lean_object* v___x_146_; 
v_name_143_ = lean_ctor_get(v_opt_142_, 0);
v_defValue_144_ = lean_ctor_get(v_opt_142_, 1);
v_map_145_ = lean_ctor_get(v_opts_141_, 0);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_145_, v_name_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_inc(v_defValue_144_);
return v_defValue_144_;
}
else
{
lean_object* v_val_147_; 
v_val_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v___x_146_, 1);
if (lean_obj_tag(v_val_147_) == 3)
{
lean_object* v_v_148_; 
v_v_148_ = lean_ctor_get(v_val_147_, 0);
lean_inc(v_v_148_);
lean_dec_ref_known(v_val_147_, 1);
return v_v_148_;
}
else
{
lean_dec(v_val_147_);
lean_inc(v_defValue_144_);
return v_defValue_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object* v_opts_149_, lean_object* v_opt_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_opts_149_, v_opt_150_);
lean_dec_ref(v_opt_150_);
lean_dec_ref(v_opts_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object* v_lctx_152_, lean_object* v_localInsts_153_, lean_object* v_x_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_152_, v_localInsts_153_, v_x_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_169_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_160_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_160_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object* v_lctx_177_, lean_object* v_localInsts_178_, lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_177_, v_localInsts_178_, v_x_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object* v_00_u03b1_186_, lean_object* v_lctx_187_, lean_object* v_localInsts_188_, lean_object* v_x_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_187_, v_localInsts_188_, v_x_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object* v_00_u03b1_196_, lean_object* v_lctx_197_, lean_object* v_localInsts_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_00_u03b1_196_, v_lctx_197_, v_localInsts_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object* v_opt_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; lean_object* v_scopes_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_opts_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_209_ = lean_st_ref_get(v___y_207_);
v_scopes_210_ = lean_ctor_get(v___x_209_, 2);
lean_inc(v_scopes_210_);
lean_dec(v___x_209_);
v___x_211_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_212_ = l_List_head_x21___redArg(v___x_211_, v_scopes_210_);
lean_dec(v_scopes_210_);
v_opts_213_ = lean_ctor_get(v___x_212_, 1);
lean_inc_ref(v_opts_213_);
lean_dec(v___x_212_);
v___x_214_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_213_, v_opt_206_);
lean_dec_ref(v_opts_213_);
v___x_215_ = lean_box(v___x_214_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object* v_opt_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v_opt_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(uint8_t v_a_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(v_a_221_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed(lean_object* v_a_230_, lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
uint8_t v_a_28877__boxed_237_; lean_object* v_res_238_; 
v_a_28877__boxed_237_ = lean_unbox(v_a_230_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(v_a_28877__boxed_237_, v_x_231_, v_x_232_, v_x_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec_ref(v_x_233_);
lean_dec_ref(v_x_232_);
lean_dec_ref(v_x_231_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(lean_object* v_postNode_239_, lean_object* v_ci_240_, lean_object* v_i_241_, lean_object* v_cs_242_, lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_247_ = lean_apply_6(v_postNode_239_, v_ci_240_, v_i_241_, v_cs_242_, v___y_244_, v___y_245_, lean_box(0));
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object* v_postNode_248_, lean_object* v_ci_249_, lean_object* v_i_250_, lean_object* v_cs_251_, lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_postNode_248_, v_ci_249_, v_i_250_, v_cs_251_, v_x_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v_x_252_);
return v_res_256_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_instMonadEIO(lean_box(0));
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_toApplicative_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_297_; 
v___x_264_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0);
v___x_265_ = l_StateRefT_x27_instMonad___redArg(v___x_264_);
v_toApplicative_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v___x_265_, 1);
lean_dec(v_unused_298_);
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_297_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_toApplicative_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_297_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_toFunctor_270_; lean_object* v_toSeq_271_; lean_object* v_toSeqLeft_272_; lean_object* v_toSeqRight_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_295_; 
v_toFunctor_270_ = lean_ctor_get(v_toApplicative_266_, 0);
v_toSeq_271_ = lean_ctor_get(v_toApplicative_266_, 2);
v_toSeqLeft_272_ = lean_ctor_get(v_toApplicative_266_, 3);
v_toSeqRight_273_ = lean_ctor_get(v_toApplicative_266_, 4);
v_isSharedCheck_295_ = !lean_is_exclusive(v_toApplicative_266_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_toApplicative_266_, 1);
lean_dec(v_unused_296_);
v___x_275_ = v_toApplicative_266_;
v_isShared_276_ = v_isSharedCheck_295_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_toSeqRight_273_);
lean_inc(v_toSeqLeft_272_);
lean_inc(v_toSeq_271_);
lean_inc(v_toFunctor_270_);
lean_dec(v_toApplicative_266_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_295_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v___f_284_; lean_object* v___x_286_; 
v___f_277_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1));
v___f_278_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2));
lean_inc_ref(v_toFunctor_270_);
v___f_279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_279_, 0, v_toFunctor_270_);
v___f_280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_280_, 0, v_toFunctor_270_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___f_279_);
lean_ctor_set(v___x_281_, 1, v___f_280_);
v___f_282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_282_, 0, v_toSeqRight_273_);
v___f_283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_283_, 0, v_toSeqLeft_272_);
v___f_284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_284_, 0, v_toSeq_271_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 4, v___f_282_);
lean_ctor_set(v___x_275_, 3, v___f_283_);
lean_ctor_set(v___x_275_, 2, v___f_284_);
lean_ctor_set(v___x_275_, 1, v___f_277_);
lean_ctor_set(v___x_275_, 0, v___x_281_);
v___x_286_ = v___x_275_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___f_277_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v___f_284_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v___f_283_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v___f_282_);
v___x_286_ = v_reuseFailAlloc_294_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___f_278_);
lean_ctor_set(v___x_268_, 0, v___x_286_);
v___x_288_ = v___x_268_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___f_278_);
v___x_288_ = v_reuseFailAlloc_293_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_25885__overap_291_; lean_object* v___x_292_; 
v___x_289_ = lean_box(0);
v___x_290_ = l_instInhabitedOfMonad___redArg(v___x_288_, v___x_289_);
v___x_25885__overap_291_ = lean_panic_fn_borrowed(v___x_290_, v_msg_260_);
lean_dec(v___x_290_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
v___x_292_ = lean_apply_3(v___x_25885__overap_291_, v___y_261_, v___y_262_, lean_box(0));
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___boxed(lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_303_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2));
v___x_308_ = lean_unsigned_to_nat(21u);
v___x_309_ = lean_unsigned_to_nat(65u);
v___x_310_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1));
v___x_311_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0));
v___x_312_ = l_mkPanicMessageWithDecl(v___x_311_, v___x_310_, v___x_309_, v___x_308_, v___x_307_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(lean_object* v_preNode_313_, lean_object* v_postNode_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
switch(lean_obj_tag(v_x_316_))
{
case 0:
{
lean_object* v_i_320_; lean_object* v_t_321_; lean_object* v___x_322_; 
v_i_320_ = lean_ctor_get(v_x_316_, 0);
lean_inc_ref(v_i_320_);
v_t_321_ = lean_ctor_get(v_x_316_, 1);
lean_inc_ref(v_t_321_);
lean_dec_ref_known(v_x_316_, 2);
v___x_322_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_320_, v_x_315_);
v_x_315_ = v___x_322_;
v_x_316_ = v_t_321_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_315_) == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec_ref_known(v_x_316_, 2);
lean_dec_ref(v_postNode_314_);
lean_dec_ref(v_preNode_313_);
v___x_324_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3);
v___x_325_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v___x_324_, v___y_317_, v___y_318_);
return v___x_325_;
}
else
{
lean_object* v_i_326_; lean_object* v_children_327_; lean_object* v_val_328_; lean_object* v___x_329_; 
v_i_326_ = lean_ctor_get(v_x_316_, 0);
lean_inc_ref_n(v_i_326_, 2);
v_children_327_ = lean_ctor_get(v_x_316_, 1);
lean_inc_ref_n(v_children_327_, 2);
lean_dec_ref_known(v_x_316_, 2);
v_val_328_ = lean_ctor_get(v_x_315_, 0);
lean_inc_n(v_val_328_, 2);
lean_inc_ref(v_preNode_313_);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v___x_329_ = lean_apply_6(v_preNode_313_, v_val_328_, v_i_326_, v_children_327_, v___y_317_, v___y_318_, lean_box(0));
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; uint8_t v___x_331_; uint8_t v___x_332_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = lean_unbox(v_a_330_);
lean_dec(v_a_330_);
v___x_332_ = lean_bool_not(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_333_ = l_Lean_Elab_Info_updateContext_x3f(v_x_315_, v_i_326_);
v___x_334_ = l_Lean_PersistentArray_toList___redArg(v_children_327_);
v___x_335_ = lean_box(0);
lean_inc_ref(v_postNode_314_);
v___x_336_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_313_, v_postNode_314_, v___x_333_, v___x_334_, v___x_335_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v___x_338_ = lean_apply_7(v_postNode_314_, v_val_328_, v_i_326_, v_children_327_, v_a_337_, v___y_317_, v___y_318_, lean_box(0));
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_347_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_a_339_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_a_348_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_338_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_338_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_val_328_);
lean_dec_ref(v_children_327_);
lean_dec_ref(v_i_326_);
lean_dec_ref(v_postNode_314_);
v_a_356_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_336_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_336_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_preNode_313_);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v_x_315_, 0);
lean_dec(v_unused_389_);
v___x_365_ = v_x_315_;
v_isShared_366_ = v_isSharedCheck_388_;
goto v_resetjp_364_;
}
else
{
lean_dec(v_x_315_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_388_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box(0);
lean_inc(v___y_318_);
lean_inc_ref(v___y_317_);
v___x_368_ = lean_apply_7(v_postNode_314_, v_val_328_, v_i_326_, v_children_327_, v___x_367_, v___y_317_, v___y_318_, lean_box(0));
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_379_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_379_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v_a_369_);
v___x_374_ = v___x_365_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_del_object(v___x_365_);
v_a_380_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_368_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_368_);
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
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_val_328_);
lean_dec_ref(v_children_327_);
lean_dec_ref_known(v_x_315_, 1);
lean_dec_ref(v_i_326_);
lean_dec_ref(v_postNode_314_);
lean_dec_ref(v_preNode_313_);
v_a_390_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_329_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_329_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
default: 
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_x_315_);
lean_dec_ref(v_postNode_314_);
lean_dec_ref(v_preNode_313_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v_x_316_, 0);
lean_dec(v_unused_406_);
v___x_399_ = v_x_316_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_x_316_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_box(0);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(lean_object* v_preNode_407_, lean_object* v_postNode_408_, lean_object* v___x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_409_);
lean_dec_ref(v_postNode_408_);
lean_dec_ref(v_preNode_407_);
v___x_415_ = l_List_reverse___redArg(v_x_411_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
else
{
lean_object* v_head_417_; lean_object* v_tail_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_436_; 
v_head_417_ = lean_ctor_get(v_x_410_, 0);
v_tail_418_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_436_ == 0)
{
v___x_420_ = v_x_410_;
v_isShared_421_ = v_isSharedCheck_436_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_tail_418_);
lean_inc(v_head_417_);
lean_dec(v_x_410_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_436_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; 
lean_inc(v___x_409_);
lean_inc_ref(v_postNode_408_);
lean_inc_ref(v_preNode_407_);
v___x_422_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_407_, v_postNode_408_, v___x_409_, v_head_417_, v___y_412_, v___y_413_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v_x_411_);
lean_ctor_set(v___x_420_, 0, v_a_423_);
v___x_425_ = v___x_420_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_423_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_x_411_);
v___x_425_ = v_reuseFailAlloc_427_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
v_x_410_ = v_tail_418_;
v_x_411_ = v___x_425_;
goto _start;
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_del_object(v___x_420_);
lean_dec(v_tail_418_);
lean_dec(v_x_411_);
lean_dec(v___x_409_);
lean_dec_ref(v_postNode_408_);
lean_dec_ref(v_preNode_407_);
v_a_428_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_422_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_422_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg___boxed(lean_object* v_preNode_437_, lean_object* v_postNode_438_, lean_object* v___x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_437_, v_postNode_438_, v___x_439_, v_x_440_, v_x_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___boxed(lean_object* v_preNode_446_, lean_object* v_postNode_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_446_, v_postNode_447_, v_x_448_, v_x_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(lean_object* v_preNode_454_, lean_object* v_postNode_455_, lean_object* v_ctx_x3f_456_, lean_object* v_t_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_462_; 
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed), 8, 1);
lean_closure_set(v___f_461_, 0, v_postNode_455_);
v___x_462_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_454_, v___f_461_, v_ctx_x3f_456_, v_t_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_462_, 0);
lean_dec(v_unused_471_);
v___x_464_ = v___x_462_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_462_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_a_472_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_462_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_462_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object* v_preNode_480_, lean_object* v_postNode_481_, lean_object* v_ctx_x3f_482_, lean_object* v_t_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_preNode_480_, v_postNode_481_, v_ctx_x3f_482_, v_t_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_487_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(uint8_t v___y_489_, uint8_t v_suppressElabErrors_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 1)
{
lean_object* v_pre_492_; 
v_pre_492_ = lean_ctor_get(v_x_491_, 0);
if (lean_obj_tag(v_pre_492_) == 0)
{
lean_object* v_str_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_str_493_ = lean_ctor_get(v_x_491_, 1);
v___x_494_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0));
v___x_495_ = lean_string_dec_eq(v_str_493_, v___x_494_);
if (v___x_495_ == 0)
{
return v___y_489_;
}
else
{
return v_suppressElabErrors_490_;
}
}
else
{
return v___y_489_;
}
}
else
{
return v___y_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed(lean_object* v___y_496_, lean_object* v_suppressElabErrors_497_, lean_object* v_x_498_){
_start:
{
uint8_t v___y_29321__boxed_499_; uint8_t v_suppressElabErrors_boxed_500_; uint8_t v_res_501_; lean_object* v_r_502_; 
v___y_29321__boxed_499_ = lean_unbox(v___y_496_);
v_suppressElabErrors_boxed_500_ = lean_unbox(v_suppressElabErrors_497_);
v_res_501_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(v___y_29321__boxed_499_, v_suppressElabErrors_boxed_500_, v_x_498_);
lean_dec(v_x_498_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0(void){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_503_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
lean_ctor_set(v___x_508_, 3, v___x_507_);
lean_ctor_set(v___x_508_, 4, v___x_506_);
lean_ctor_set(v___x_508_, 5, v___x_506_);
lean_ctor_set(v___x_508_, 6, v___x_506_);
lean_ctor_set(v___x_508_, 7, v___x_506_);
lean_ctor_set(v___x_508_, 8, v___x_506_);
lean_ctor_set(v___x_508_, 9, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_unsigned_to_nat(32u);
v___x_510_ = lean_mk_empty_array_with_capacity(v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4(void){
_start:
{
size_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_512_ = ((size_t)5ULL);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_unsigned_to_nat(32u);
v___x_515_ = lean_mk_empty_array_with_capacity(v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3);
v___x_517_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_515_);
lean_ctor_set(v___x_517_, 2, v___x_513_);
lean_ctor_set(v___x_517_, 3, v___x_513_);
lean_ctor_set_usize(v___x_517_, 4, v___x_512_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_box(1);
v___x_519_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_520_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_518_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(lean_object* v_msgData_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_env_526_; lean_object* v___x_527_; lean_object* v_scopes_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_opts_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_525_ = lean_st_ref_get(v___y_523_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_525_);
v___x_527_ = lean_st_ref_get(v___y_523_);
v_scopes_528_ = lean_ctor_get(v___x_527_, 2);
lean_inc(v_scopes_528_);
lean_dec(v___x_527_);
v___x_529_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_530_ = l_List_head_x21___redArg(v___x_529_, v_scopes_528_);
lean_dec(v_scopes_528_);
v_opts_531_ = lean_ctor_get(v___x_530_, 1);
lean_inc_ref(v_opts_531_);
lean_dec(v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2);
v___x_533_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5);
v___x_534_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_534_, 0, v_env_526_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
lean_ctor_set(v___x_534_, 3, v_opts_531_);
v___x_535_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_msgData_522_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___boxed(lean_object* v_msgData_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_537_, v___y_538_);
lean_dec(v___y_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(lean_object* v_ref_542_, lean_object* v_msgData_543_, uint8_t v_severity_544_, uint8_t v_isSilent_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___y_550_; uint8_t v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; uint8_t v___y_641_; uint8_t v___y_642_; uint8_t v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_649_; uint8_t v___y_650_; uint8_t v___y_651_; uint8_t v___x_666_; uint8_t v___y_668_; uint8_t v___y_669_; uint8_t v___y_670_; uint8_t v___y_672_; uint8_t v___x_684_; 
v___x_666_ = 2;
v___x_684_ = l_Lean_instBEqMessageSeverity_beq(v_severity_544_, v___x_666_);
if (v___x_684_ == 0)
{
v___y_672_ = v___x_684_;
goto v___jp_671_;
}
else
{
uint8_t v___x_685_; 
lean_inc_ref(v_msgData_543_);
v___x_685_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_543_);
v___y_672_ = v___x_685_;
goto v___jp_671_;
}
v___jp_549_:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Elab_Command_getScope___redArg(v___y_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = l_Lean_Elab_Command_getScope___redArg(v___y_557_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_595_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_595_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_595_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_595_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v_currNamespace_566_; lean_object* v_openDecls_567_; lean_object* v_env_568_; lean_object* v_messages_569_; lean_object* v_scopes_570_; lean_object* v_usedQuotCtxts_571_; lean_object* v_nextMacroScope_572_; lean_object* v_maxRecDepth_573_; lean_object* v_ngen_574_; lean_object* v_auxDeclNGen_575_; lean_object* v_infoState_576_; lean_object* v_traceState_577_; lean_object* v_snapshotTasks_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_594_; 
v___x_565_ = lean_st_ref_take(v___y_557_);
v_currNamespace_566_ = lean_ctor_get(v_a_559_, 2);
lean_inc(v_currNamespace_566_);
lean_dec(v_a_559_);
v_openDecls_567_ = lean_ctor_get(v_a_561_, 3);
lean_inc(v_openDecls_567_);
lean_dec(v_a_561_);
v_env_568_ = lean_ctor_get(v___x_565_, 0);
v_messages_569_ = lean_ctor_get(v___x_565_, 1);
v_scopes_570_ = lean_ctor_get(v___x_565_, 2);
v_usedQuotCtxts_571_ = lean_ctor_get(v___x_565_, 3);
v_nextMacroScope_572_ = lean_ctor_get(v___x_565_, 4);
v_maxRecDepth_573_ = lean_ctor_get(v___x_565_, 5);
v_ngen_574_ = lean_ctor_get(v___x_565_, 6);
v_auxDeclNGen_575_ = lean_ctor_get(v___x_565_, 7);
v_infoState_576_ = lean_ctor_get(v___x_565_, 8);
v_traceState_577_ = lean_ctor_get(v___x_565_, 9);
v_snapshotTasks_578_ = lean_ctor_get(v___x_565_, 10);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_594_ == 0)
{
v___x_580_ = v___x_565_;
v_isShared_581_ = v_isSharedCheck_594_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snapshotTasks_578_);
lean_inc(v_traceState_577_);
lean_inc(v_infoState_576_);
lean_inc(v_auxDeclNGen_575_);
lean_inc(v_ngen_574_);
lean_inc(v_maxRecDepth_573_);
lean_inc(v_nextMacroScope_572_);
lean_inc(v_usedQuotCtxts_571_);
lean_inc(v_scopes_570_);
lean_inc(v_messages_569_);
lean_inc(v_env_568_);
lean_dec(v___x_565_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_594_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_currNamespace_566_);
lean_ctor_set(v___x_582_, 1, v_openDecls_567_);
v___x_583_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___y_550_);
lean_inc_ref(v___y_554_);
lean_inc_ref(v___y_556_);
v___x_584_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_584_, 0, v___y_556_);
lean_ctor_set(v___x_584_, 1, v___y_552_);
lean_ctor_set(v___x_584_, 2, v___y_553_);
lean_ctor_set(v___x_584_, 3, v___y_554_);
lean_ctor_set(v___x_584_, 4, v___x_583_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*5, v___y_555_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*5 + 1, v___y_551_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*5 + 2, v_isSilent_545_);
v___x_585_ = l_Lean_MessageLog_add(v___x_584_, v_messages_569_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_585_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_env_568_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_scopes_570_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_usedQuotCtxts_571_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_nextMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_593_, 5, v_maxRecDepth_573_);
lean_ctor_set(v_reuseFailAlloc_593_, 6, v_ngen_574_);
lean_ctor_set(v_reuseFailAlloc_593_, 7, v_auxDeclNGen_575_);
lean_ctor_set(v_reuseFailAlloc_593_, 8, v_infoState_576_);
lean_ctor_set(v_reuseFailAlloc_593_, 9, v_traceState_577_);
lean_ctor_set(v_reuseFailAlloc_593_, 10, v_snapshotTasks_578_);
v___x_587_ = v_reuseFailAlloc_593_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_st_ref_set(v___y_557_, v___x_587_);
v___x_589_ = lean_box(0);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_589_);
v___x_591_ = v___x_563_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_a_559_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_550_);
v_a_596_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_560_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_560_);
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
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_550_);
v_a_604_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_558_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_558_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
v___jp_612_:
{
lean_object* v_fileName_618_; lean_object* v_fileMap_619_; uint8_t v_suppressElabErrors_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_639_; 
v_fileName_618_ = lean_ctor_get(v___y_546_, 0);
v_fileMap_619_ = lean_ctor_get(v___y_546_, 1);
v_suppressElabErrors_620_ = lean_ctor_get_uint8(v___y_546_, sizeof(void*)*10);
v___x_621_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_543_);
v___x_622_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v___x_621_, v___y_547_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_639_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_639_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_639_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc_ref_n(v_fileMap_619_, 2);
v___x_627_ = l_Lean_FileMap_toPosition(v_fileMap_619_, v___y_614_);
lean_dec(v___y_614_);
v___x_628_ = l_Lean_FileMap_toPosition(v_fileMap_619_, v___y_617_);
lean_dec(v___y_617_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0));
if (v_suppressElabErrors_620_ == 0)
{
lean_del_object(v___x_625_);
v___y_550_ = v_a_623_;
v___y_551_ = v___y_615_;
v___y_552_ = v___x_627_;
v___y_553_ = v___x_629_;
v___y_554_ = v___x_630_;
v___y_555_ = v___y_616_;
v___y_556_ = v_fileName_618_;
v___y_557_ = v___y_547_;
goto v___jp_549_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___f_633_; uint8_t v___x_634_; 
v___x_631_ = lean_box(v___y_613_);
v___x_632_ = lean_box(v_suppressElabErrors_620_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed), 3, 2);
lean_closure_set(v___f_633_, 0, v___x_631_);
lean_closure_set(v___f_633_, 1, v___x_632_);
lean_inc(v_a_623_);
v___x_634_ = l_Lean_MessageData_hasTag(v___f_633_, v_a_623_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec_ref_known(v___x_629_, 1);
lean_dec_ref(v___x_627_);
lean_dec(v_a_623_);
v___x_635_ = lean_box(0);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_635_);
v___x_637_ = v___x_625_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_del_object(v___x_625_);
v___y_550_ = v_a_623_;
v___y_551_ = v___y_615_;
v___y_552_ = v___x_627_;
v___y_553_ = v___x_629_;
v___y_554_ = v___x_630_;
v___y_555_ = v___y_616_;
v___y_556_ = v_fileName_618_;
v___y_557_ = v___y_547_;
goto v___jp_549_;
}
}
}
}
v___jp_640_:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Syntax_getTailPos_x3f(v___y_644_, v___y_643_);
lean_dec(v___y_644_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_inc(v___y_645_);
v___y_613_ = v___y_641_;
v___y_614_ = v___y_645_;
v___y_615_ = v___y_642_;
v___y_616_ = v___y_643_;
v___y_617_ = v___y_645_;
goto v___jp_612_;
}
else
{
lean_object* v_val_647_; 
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_646_, 1);
v___y_613_ = v___y_641_;
v___y_614_ = v___y_645_;
v___y_615_ = v___y_642_;
v___y_616_ = v___y_643_;
v___y_617_ = v_val_647_;
goto v___jp_612_;
}
}
v___jp_648_:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Elab_Command_getRef___redArg(v___y_546_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_ref_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v_ref_654_ = l_Lean_replaceRef(v_ref_542_, v_a_653_);
lean_dec(v_a_653_);
v___x_655_ = l_Lean_Syntax_getPos_x3f(v_ref_654_, v___y_650_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___y_641_ = v___y_649_;
v___y_642_ = v___y_651_;
v___y_643_ = v___y_650_;
v___y_644_ = v_ref_654_;
v___y_645_ = v___x_656_;
goto v___jp_640_;
}
else
{
lean_object* v_val_657_; 
v_val_657_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v___x_655_, 1);
v___y_641_ = v___y_649_;
v___y_642_ = v___y_651_;
v___y_643_ = v___y_650_;
v___y_644_ = v_ref_654_;
v___y_645_ = v_val_657_;
goto v___jp_640_;
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_msgData_543_);
v_a_658_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_652_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_652_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
v___jp_667_:
{
if (v___y_670_ == 0)
{
v___y_649_ = v___y_668_;
v___y_650_ = v___y_669_;
v___y_651_ = v_severity_544_;
goto v___jp_648_;
}
else
{
v___y_649_ = v___y_668_;
v___y_650_ = v___y_669_;
v___y_651_ = v___x_666_;
goto v___jp_648_;
}
}
v___jp_671_:
{
if (v___y_672_ == 0)
{
lean_object* v___x_673_; lean_object* v_scopes_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_opts_677_; uint8_t v___x_678_; uint8_t v___x_679_; 
v___x_673_ = lean_st_ref_get(v___y_547_);
v_scopes_674_ = lean_ctor_get(v___x_673_, 2);
lean_inc(v_scopes_674_);
lean_dec(v___x_673_);
v___x_675_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_676_ = l_List_head_x21___redArg(v___x_675_, v_scopes_674_);
lean_dec(v_scopes_674_);
v_opts_677_ = lean_ctor_get(v___x_676_, 1);
lean_inc_ref(v_opts_677_);
lean_dec(v___x_676_);
v___x_678_ = 1;
v___x_679_ = l_Lean_instBEqMessageSeverity_beq(v_severity_544_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec_ref(v_opts_677_);
v___y_668_ = v___y_672_;
v___y_669_ = v___y_672_;
v___y_670_ = v___x_679_;
goto v___jp_667_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = l_Lean_warningAsError;
v___x_681_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_677_, v___x_680_);
lean_dec_ref(v_opts_677_);
v___y_668_ = v___y_672_;
v___y_669_ = v___y_672_;
v___y_670_ = v___x_681_;
goto v___jp_667_;
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref(v_msgData_543_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___boxed(lean_object* v_ref_686_, lean_object* v_msgData_687_, lean_object* v_severity_688_, lean_object* v_isSilent_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
uint8_t v_severity_boxed_693_; uint8_t v_isSilent_boxed_694_; lean_object* v_res_695_; 
v_severity_boxed_693_ = lean_unbox(v_severity_688_);
v_isSilent_boxed_694_ = lean_unbox(v_isSilent_689_);
v_res_695_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_686_, v_msgData_687_, v_severity_boxed_693_, v_isSilent_boxed_694_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v_ref_686_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(lean_object* v_ref_696_, lean_object* v_msgData_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = 1;
v___x_702_ = 0;
v___x_703_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_696_, v_msgData_697_, v___x_701_, v___x_702_, v___y_698_, v___y_699_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15___boxed(lean_object* v_ref_704_, lean_object* v_msgData_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_ref_704_, v_msgData_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v_ref_704_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object* v_linterOption_716_, lean_object* v_stx_717_, lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_name_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_740_; 
v_name_722_ = lean_ctor_get(v_linterOption_716_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_linterOption_716_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_linterOption_716_, 1);
lean_dec(v_unused_741_);
v___x_724_ = v_linterOption_716_;
v_isShared_725_ = v_isSharedCheck_740_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_name_722_);
lean_dec(v_linterOption_716_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_740_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1);
lean_inc(v_name_722_);
v___x_727_ = l_Lean_MessageData_ofName(v_name_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 7);
lean_ctor_set(v___x_724_, 1, v___x_727_);
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_739_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_disable_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_730_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v_disable_732_ = l_Lean_MessageData_note(v___x_731_);
v___x_733_ = l_Lean_Linter_linterMessageTag;
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v_msg_718_);
lean_ctor_set(v___x_734_, 1, v_disable_732_);
v___x_735_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_736_, 0, v_name_722_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
lean_inc(v_stx_717_);
v___x_737_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_737_, 0, v_stx_717_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_stx_717_, v___x_737_, v___y_719_, v___y_720_);
lean_dec(v_stx_717_);
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object* v_linterOption_742_, lean_object* v_stx_743_, lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_linterOption_742_, v_stx_743_, v_msg_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_748_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0(void){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_749_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = lean_box(1);
v___x_753_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
lean_ctor_set(v___x_755_, 2, v___x_752_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(lean_object* v_val_758_, uint8_t v_a_759_, lean_object* v___x_760_, lean_object* v___f_761_, lean_object* v_ci_762_, lean_object* v_info_763_, lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_st_ref_get(v_val_758_);
v___x_769_ = lean_unbox(v___x_768_);
lean_dec(v___x_768_);
if (v___x_769_ == 0)
{
if (lean_obj_tag(v_info_763_) == 0)
{
lean_object* v_toCommandContextInfo_770_; lean_object* v_i_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_846_; 
v_toCommandContextInfo_770_ = lean_ctor_get(v_ci_762_, 0);
lean_inc_ref(v_toCommandContextInfo_770_);
v_i_771_ = lean_ctor_get(v_info_763_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_info_763_);
if (v_isSharedCheck_846_ == 0)
{
v___x_773_ = v_info_763_;
v_isShared_774_ = v_isSharedCheck_846_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_i_771_);
lean_dec(v_info_763_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_846_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_parentDecl_x3f_775_; lean_object* v_autoImplicits_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_844_; 
v_parentDecl_x3f_775_ = lean_ctor_get(v_ci_762_, 1);
v_autoImplicits_776_ = lean_ctor_get(v_ci_762_, 2);
v_isSharedCheck_844_ = !lean_is_exclusive(v_ci_762_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_ci_762_, 0);
lean_dec(v_unused_845_);
v___x_778_ = v_ci_762_;
v_isShared_779_ = v_isSharedCheck_844_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_autoImplicits_776_);
lean_inc(v_parentDecl_x3f_775_);
lean_dec(v_ci_762_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_844_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_env_780_; lean_object* v_cmdEnv_x3f_781_; lean_object* v_fileMap_782_; lean_object* v_options_783_; lean_object* v_currNamespace_784_; lean_object* v_openDecls_785_; lean_object* v_ngen_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_842_; 
v_env_780_ = lean_ctor_get(v_toCommandContextInfo_770_, 0);
v_cmdEnv_x3f_781_ = lean_ctor_get(v_toCommandContextInfo_770_, 1);
v_fileMap_782_ = lean_ctor_get(v_toCommandContextInfo_770_, 2);
v_options_783_ = lean_ctor_get(v_toCommandContextInfo_770_, 4);
v_currNamespace_784_ = lean_ctor_get(v_toCommandContextInfo_770_, 5);
v_openDecls_785_ = lean_ctor_get(v_toCommandContextInfo_770_, 6);
v_ngen_786_ = lean_ctor_get(v_toCommandContextInfo_770_, 7);
v_isSharedCheck_842_ = !lean_is_exclusive(v_toCommandContextInfo_770_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_toCommandContextInfo_770_, 3);
lean_dec(v_unused_843_);
v___x_788_ = v_toCommandContextInfo_770_;
v_isShared_789_ = v_isSharedCheck_842_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_ngen_786_);
lean_inc(v_openDecls_785_);
lean_inc(v_currNamespace_784_);
lean_inc(v_options_783_);
lean_inc(v_fileMap_782_);
lean_inc(v_cmdEnv_x3f_781_);
lean_inc(v_env_780_);
lean_dec(v_toCommandContextInfo_770_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_842_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_toElabInfo_790_; lean_object* v_mctxBefore_791_; lean_object* v_goalsBefore_792_; lean_object* v_mctxAfter_793_; lean_object* v_goalsAfter_794_; lean_object* v___y_796_; lean_object* v___x_827_; 
v_toElabInfo_790_ = lean_ctor_get(v_i_771_, 0);
lean_inc_ref(v_toElabInfo_790_);
v_mctxBefore_791_ = lean_ctor_get(v_i_771_, 1);
lean_inc_ref(v_mctxBefore_791_);
v_goalsBefore_792_ = lean_ctor_get(v_i_771_, 2);
lean_inc(v_goalsBefore_792_);
v_mctxAfter_793_ = lean_ctor_get(v_i_771_, 3);
lean_inc_ref(v_mctxAfter_793_);
v_goalsAfter_794_ = lean_ctor_get(v_i_771_, 4);
lean_inc(v_goalsAfter_794_);
lean_dec_ref(v_i_771_);
lean_inc_ref(v_ngen_786_);
lean_inc(v_openDecls_785_);
lean_inc(v_currNamespace_784_);
lean_inc_ref(v_options_783_);
lean_inc_ref(v_fileMap_782_);
lean_inc(v_cmdEnv_x3f_781_);
lean_inc_ref(v_env_780_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 3, v_mctxBefore_791_);
v___x_827_ = v___x_788_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_env_780_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_cmdEnv_x3f_781_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_fileMap_782_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_mctxBefore_791_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_options_783_);
lean_ctor_set(v_reuseFailAlloc_841_, 5, v_currNamespace_784_);
lean_ctor_set(v_reuseFailAlloc_841_, 6, v_openDecls_785_);
lean_ctor_set(v_reuseFailAlloc_841_, 7, v_ngen_786_);
v___x_827_ = v_reuseFailAlloc_841_;
goto v_reusejp_826_;
}
v___jp_795_:
{
if (lean_obj_tag(v___y_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_810_; 
lean_del_object(v___x_773_);
v_a_797_ = lean_ctor_get(v___y_796_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___y_796_);
if (v_isSharedCheck_810_ == 0)
{
v___x_799_ = v___y_796_;
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___y_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
if (lean_obj_tag(v_a_797_) == 1)
{
lean_object* v_val_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_stx_804_; lean_object* v___x_805_; 
lean_del_object(v___x_799_);
v_val_801_ = lean_ctor_get(v_a_797_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_797_, 1);
v___x_802_ = lean_box(v_a_759_);
v___x_803_ = lean_st_ref_set(v_val_758_, v___x_802_);
v_stx_804_ = lean_ctor_get(v_toElabInfo_790_, 1);
lean_inc(v_stx_804_);
lean_dec_ref(v_toElabInfo_790_);
v___x_805_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___x_760_, v_stx_804_, v_val_801_, v___y_765_, v___y_766_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_a_797_);
lean_dec_ref(v_toElabInfo_790_);
lean_dec_ref(v___x_760_);
v___x_806_ = lean_box(0);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v_toElabInfo_790_);
lean_dec_ref(v___x_760_);
v_a_811_ = lean_ctor_get(v___y_796_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___y_796_);
if (v_isSharedCheck_825_ == 0)
{
v___x_813_ = v___y_796_;
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___y_796_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_ref_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v_ref_815_ = lean_ctor_get(v___y_765_, 7);
v___x_816_ = lean_io_error_to_string(v_a_811_);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 3);
lean_ctor_set(v___x_773_, 0, v___x_816_);
v___x_818_ = v___x_773_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_824_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = l_Lean_MessageData_ofFormat(v___x_818_);
lean_inc(v_ref_815_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_ref_815_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_820_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
lean_inc_ref(v_autoImplicits_776_);
lean_inc(v_parentDecl_x3f_775_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_827_);
v___x_829_ = v___x_778_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_parentDecl_x3f_775_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_autoImplicits_776_);
v___x_829_ = v_reuseFailAlloc_840_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_830_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2);
v___x_831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3));
lean_inc_ref(v___f_761_);
v___x_832_ = lean_apply_2(v___f_761_, v___x_831_, v_goalsBefore_792_);
v___x_833_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_829_, v___x_830_, v___x_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_835_, 0, v_env_780_);
lean_ctor_set(v___x_835_, 1, v_cmdEnv_x3f_781_);
lean_ctor_set(v___x_835_, 2, v_fileMap_782_);
lean_ctor_set(v___x_835_, 3, v_mctxAfter_793_);
lean_ctor_set(v___x_835_, 4, v_options_783_);
lean_ctor_set(v___x_835_, 5, v_currNamespace_784_);
lean_ctor_set(v___x_835_, 6, v_openDecls_785_);
lean_ctor_set(v___x_835_, 7, v_ngen_786_);
v___x_836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_parentDecl_x3f_775_);
lean_ctor_set(v___x_836_, 2, v_autoImplicits_776_);
v___x_837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4));
v___x_838_ = lean_apply_2(v___f_761_, v___x_837_, v_goalsAfter_794_);
v___x_839_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_836_, v___x_830_, v___x_838_);
v___y_796_ = v___x_839_;
goto v___jp_795_;
}
else
{
lean_dec_ref_known(v_a_834_, 1);
lean_dec(v_goalsAfter_794_);
lean_dec_ref(v_mctxAfter_793_);
lean_dec_ref(v_ngen_786_);
lean_dec(v_openDecls_785_);
lean_dec(v_currNamespace_784_);
lean_dec_ref(v_options_783_);
lean_dec_ref(v_fileMap_782_);
lean_dec(v_cmdEnv_x3f_781_);
lean_dec_ref(v_env_780_);
lean_dec_ref(v_autoImplicits_776_);
lean_dec(v_parentDecl_x3f_775_);
lean_dec_ref(v___f_761_);
v___y_796_ = v___x_833_;
goto v___jp_795_;
}
}
else
{
lean_dec(v_goalsAfter_794_);
lean_dec_ref(v_mctxAfter_793_);
lean_dec_ref(v_ngen_786_);
lean_dec(v_openDecls_785_);
lean_dec(v_currNamespace_784_);
lean_dec_ref(v_options_783_);
lean_dec_ref(v_fileMap_782_);
lean_dec(v_cmdEnv_x3f_781_);
lean_dec_ref(v_env_780_);
lean_dec_ref(v_autoImplicits_776_);
lean_dec(v_parentDecl_x3f_775_);
lean_dec_ref(v___f_761_);
v___y_796_ = v___x_833_;
goto v___jp_795_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v_info_763_);
lean_dec_ref(v_ci_762_);
lean_dec_ref(v___f_761_);
lean_dec_ref(v___x_760_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec_ref(v_info_763_);
lean_dec_ref(v_ci_762_);
lean_dec_ref(v___f_761_);
lean_dec_ref(v___x_760_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed(lean_object* v_val_851_, lean_object* v_a_852_, lean_object* v___x_853_, lean_object* v___f_854_, lean_object* v_ci_855_, lean_object* v_info_856_, lean_object* v_x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
uint8_t v_a_29795__boxed_861_; lean_object* v_res_862_; 
v_a_29795__boxed_861_ = lean_unbox(v_a_852_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(v_val_851_, v_a_29795__boxed_861_, v___x_853_, v___f_854_, v_ci_855_, v_info_856_, v_x_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_x_857_);
lean_dec(v_val_851_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(lean_object* v___x_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
if (lean_obj_tag(v_a_864_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref(v___x_863_);
v___x_866_ = lean_array_to_list(v_a_865_);
return v___x_866_;
}
else
{
lean_object* v_head_867_; lean_object* v_tail_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_head_867_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_head_867_);
v_tail_868_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_tail_868_);
lean_dec_ref_known(v_a_864_, 2);
v_fst_869_ = lean_ctor_get(v_head_867_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v_head_867_, 1);
lean_inc(v_snd_870_);
lean_dec(v_head_867_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_nat_dec_lt(v___x_871_, v_snd_870_);
lean_dec(v_snd_870_);
if (v___x_872_ == 0)
{
lean_dec(v_fst_869_);
v_a_864_ = v_tail_868_;
goto _start;
}
else
{
uint8_t v___x_874_; 
lean_inc(v_fst_869_);
lean_inc_ref(v___x_863_);
v___x_874_ = l_Lean_getReducibilityStatusCore(v___x_863_, v_fst_869_);
if (v___x_874_ == 1)
{
uint8_t v___x_875_; uint8_t v___x_876_; 
lean_inc_ref(v___x_863_);
v___x_875_ = l_Lean_Meta_isInstanceCore(v___x_863_, v_fst_869_);
v___x_876_ = lean_bool_not(v___x_875_);
if (v___x_876_ == 0)
{
lean_dec(v_fst_869_);
v_a_864_ = v_tail_868_;
goto _start;
}
else
{
uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = 0;
v___x_879_ = l_Lean_MessageData_ofConstName(v_fst_869_, v___x_878_);
v___x_880_ = lean_array_push(v_a_865_, v___x_879_);
v_a_864_ = v_tail_868_;
v_a_865_ = v___x_880_;
goto _start;
}
}
else
{
lean_dec(v_fst_869_);
v_a_864_ = v_tail_868_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(lean_object* v_o_885_, lean_object* v_k_886_, uint8_t v_v_887_){
_start:
{
lean_object* v_map_888_; uint8_t v_hasTrace_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_903_; 
v_map_888_ = lean_ctor_get(v_o_885_, 0);
v_hasTrace_889_ = lean_ctor_get_uint8(v_o_885_, sizeof(void*)*1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_o_885_);
if (v_isSharedCheck_903_ == 0)
{
v___x_891_ = v_o_885_;
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_map_888_);
lean_dec(v_o_885_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_903_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_893_, 0, v_v_887_);
lean_inc(v_k_886_);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_886_, v___x_893_, v_map_888_);
if (v_hasTrace_889_ == 0)
{
lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_898_; 
v___x_895_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0));
v___x_896_ = l_Lean_Name_isPrefixOf(v___x_895_, v_k_886_);
lean_dec(v_k_886_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_898_ = v___x_891_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_894_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*1, v___x_896_);
return v___x_898_;
}
}
else
{
lean_object* v___x_901_; 
lean_dec(v_k_886_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_901_ = v___x_891_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_902_, sizeof(void*)*1, v_hasTrace_889_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___boxed(lean_object* v_o_904_, lean_object* v_k_905_, lean_object* v_v_906_){
_start:
{
uint8_t v_v_boxed_907_; lean_object* v_res_908_; 
v_v_boxed_907_ = lean_unbox(v_v_906_);
v_res_908_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_o_904_, v_k_905_, v_v_boxed_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(lean_object* v_opts_909_, lean_object* v_opt_910_, uint8_t v_val_911_){
_start:
{
lean_object* v_name_912_; lean_object* v___x_913_; 
v_name_912_ = lean_ctor_get(v_opt_910_, 0);
lean_inc(v_name_912_);
lean_dec_ref(v_opt_910_);
v___x_913_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_opts_909_, v_name_912_, v_val_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(lean_object* v_opts_914_, lean_object* v_opt_915_, lean_object* v_val_916_){
_start:
{
uint8_t v_val_boxed_917_; lean_object* v_res_918_; 
v_val_boxed_917_ = lean_unbox(v_val_916_);
v_res_918_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_opts_914_, v_opt_915_, v_val_boxed_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(lean_object* v_f_919_, lean_object* v_keys_920_, lean_object* v_vals_921_, lean_object* v_i_922_, lean_object* v_acc_923_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_array_get_size(v_keys_920_);
v___x_925_ = lean_nat_dec_lt(v_i_922_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec(v_i_922_);
lean_dec_ref(v_f_919_);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v_acc_923_);
return v___x_926_;
}
else
{
lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v___x_929_; 
v_k_927_ = lean_array_fget_borrowed(v_keys_920_, v_i_922_);
v_v_928_ = lean_array_fget_borrowed(v_vals_921_, v_i_922_);
lean_inc_ref(v_f_919_);
lean_inc(v_v_928_);
lean_inc(v_k_927_);
v___x_929_ = lean_apply_3(v_f_919_, v_acc_923_, v_k_927_, v_v_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_dec(v_i_922_);
lean_dec_ref(v_f_919_);
return v___x_929_;
}
else
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_add(v_i_922_, v___x_931_);
lean_dec(v_i_922_);
v_i_922_ = v___x_932_;
v_acc_923_ = v_a_930_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg___boxed(lean_object* v_f_934_, lean_object* v_keys_935_, lean_object* v_vals_936_, lean_object* v_i_937_, lean_object* v_acc_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_934_, v_keys_935_, v_vals_936_, v_i_937_, v_acc_938_);
lean_dec_ref(v_vals_936_);
lean_dec_ref(v_keys_935_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(lean_object* v_f_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
lean_object* v_es_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_963_; 
v_es_943_ = lean_ctor_get(v_x_941_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_941_);
if (v_isSharedCheck_963_ == 0)
{
v___x_945_ = v_x_941_;
v_isShared_946_ = v_isSharedCheck_963_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_es_943_);
lean_dec(v_x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_963_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_array_get_size(v_es_943_);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v_es_943_);
lean_dec_ref(v_f_940_);
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
lean_ctor_set(v___x_945_, 0, v_x_942_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_x_942_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
uint8_t v___x_953_; 
v___x_953_ = lean_nat_dec_le(v___x_948_, v___x_948_);
if (v___x_953_ == 0)
{
if (v___x_949_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v_es_943_);
lean_dec_ref(v_f_940_);
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
lean_ctor_set(v___x_945_, 0, v_x_942_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_x_942_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
lean_del_object(v___x_945_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = lean_usize_of_nat(v___x_948_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_940_, v_es_943_, v___x_957_, v___x_958_, v_x_942_);
lean_dec_ref(v_es_943_);
return v___x_959_;
}
}
else
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
lean_del_object(v___x_945_);
v___x_960_ = ((size_t)0ULL);
v___x_961_ = lean_usize_of_nat(v___x_948_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_940_, v_es_943_, v___x_960_, v___x_961_, v_x_942_);
lean_dec_ref(v_es_943_);
return v___x_962_;
}
}
}
}
else
{
lean_object* v_ks_964_; lean_object* v_vs_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_ks_964_ = lean_ctor_get(v_x_941_, 0);
lean_inc_ref(v_ks_964_);
v_vs_965_ = lean_ctor_get(v_x_941_, 1);
lean_inc_ref(v_vs_965_);
lean_dec_ref_known(v_x_941_, 2);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_940_, v_ks_964_, v_vs_965_, v___x_966_, v_x_942_);
lean_dec_ref(v_vs_965_);
lean_dec_ref(v_ks_964_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(lean_object* v_f_968_, lean_object* v_as_969_, size_t v_i_970_, size_t v_stop_971_, lean_object* v_b_972_){
_start:
{
lean_object* v_a_974_; lean_object* v___y_979_; uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_eq(v_i_970_, v_stop_971_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_array_uget_borrowed(v_as_969_, v_i_970_);
switch(lean_obj_tag(v___x_982_))
{
case 0:
{
lean_object* v_key_983_; lean_object* v_val_984_; lean_object* v___x_985_; 
v_key_983_ = lean_ctor_get(v___x_982_, 0);
v_val_984_ = lean_ctor_get(v___x_982_, 1);
lean_inc_ref(v_f_968_);
lean_inc(v_val_984_);
lean_inc(v_key_983_);
v___x_985_ = lean_apply_3(v_f_968_, v_b_972_, v_key_983_, v_val_984_);
v___y_979_ = v___x_985_;
goto v___jp_978_;
}
case 1:
{
lean_object* v_node_986_; lean_object* v___x_987_; 
v_node_986_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_node_986_);
lean_inc_ref(v_f_968_);
v___x_987_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_968_, v_node_986_, v_b_972_);
v___y_979_ = v___x_987_;
goto v___jp_978_;
}
default: 
{
v_a_974_ = v_b_972_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v___x_988_; 
lean_dec_ref(v_f_968_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_b_972_);
return v___x_988_;
}
v___jp_973_:
{
size_t v___x_975_; size_t v___x_976_; 
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_970_, v___x_975_);
v_i_970_ = v___x_976_;
v_b_972_ = v_a_974_;
goto _start;
}
v___jp_978_:
{
if (lean_obj_tag(v___y_979_) == 0)
{
lean_dec_ref(v_f_968_);
return v___y_979_;
}
else
{
lean_object* v_a_980_; 
v_a_980_ = lean_ctor_get(v___y_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___y_979_, 1);
v_a_974_ = v_a_980_;
goto v___jp_973_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg___boxed(lean_object* v_f_989_, lean_object* v_as_990_, lean_object* v_i_991_, lean_object* v_stop_992_, lean_object* v_b_993_){
_start:
{
size_t v_i_boxed_994_; size_t v_stop_boxed_995_; lean_object* v_res_996_; 
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_stop_boxed_995_ = lean_unbox_usize(v_stop_992_);
lean_dec(v_stop_992_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_989_, v_as_990_, v_i_boxed_994_, v_stop_boxed_995_, v_b_993_);
lean_dec_ref(v_as_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0(lean_object* v_f_997_, lean_object* v_s_998_, lean_object* v_a_999_, lean_object* v_b_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_a_999_);
lean_ctor_set(v___x_1001_, 1, v_b_1000_);
v___x_1002_ = lean_apply_2(v_f_997_, v___x_1001_, v_s_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(lean_object* v_map_1019_, lean_object* v_init_1020_, lean_object* v_f_1021_){
_start:
{
lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; 
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1022_, 0, v_f_1021_);
lean_inc_ref(v_map_1019_);
v___x_1023_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v___f_1022_, v_map_1019_, v_init_1020_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
return v_a_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___boxed(lean_object* v_map_1025_, lean_object* v_init_1026_, lean_object* v_f_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_1025_, v_init_1026_, v_f_1027_);
lean_dec_ref(v_map_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_ks_1033_; lean_object* v_vs_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1058_; 
v_ks_1033_ = lean_ctor_get(v_x_1029_, 0);
v_vs_1034_ = lean_ctor_get(v_x_1029_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1029_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1036_ = v_x_1029_;
v_isShared_1037_ = v_isSharedCheck_1058_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_vs_1034_);
lean_inc(v_ks_1033_);
lean_dec(v_x_1029_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1058_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_array_get_size(v_ks_1033_);
v___x_1039_ = lean_nat_dec_lt(v_x_1030_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_dec(v_x_1030_);
v___x_1040_ = lean_array_push(v_ks_1033_, v_x_1031_);
v___x_1041_ = lean_array_push(v_vs_1034_, v_x_1032_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1041_);
lean_ctor_set(v___x_1036_, 0, v___x_1040_);
v___x_1043_ = v___x_1036_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
else
{
lean_object* v_k_x27_1045_; uint8_t v___x_1046_; 
v_k_x27_1045_ = lean_array_fget_borrowed(v_ks_1033_, v_x_1030_);
v___x_1046_ = lean_name_eq(v_x_1031_, v_k_x27_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1048_; 
if (v_isShared_1037_ == 0)
{
v___x_1048_ = v___x_1036_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_ks_1033_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_vs_1034_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_nat_add(v_x_1030_, v___x_1049_);
lean_dec(v_x_1030_);
v_x_1029_ = v___x_1048_;
v_x_1030_ = v___x_1050_;
goto _start;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = lean_array_fset(v_ks_1033_, v_x_1030_, v_x_1031_);
v___x_1054_ = lean_array_fset(v_vs_1034_, v_x_1030_, v_x_1032_);
lean_dec(v_x_1030_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1054_);
lean_ctor_set(v___x_1036_, 0, v___x_1053_);
v___x_1056_ = v___x_1036_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(lean_object* v_n_1059_, lean_object* v_k_1060_, lean_object* v_v_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_n_1059_, v___x_1062_, v_k_1060_, v_v_1061_);
return v___x_1063_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1064_; uint64_t v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(1723u);
v___x_1065_ = lean_uint64_of_nat(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(lean_object* v_x_1067_, size_t v_x_1068_, size_t v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v_es_1072_; size_t v___x_1073_; size_t v___x_1074_; lean_object* v_j_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_es_1072_ = lean_ctor_get(v_x_1067_, 0);
v___x_1073_ = ((size_t)31ULL);
v___x_1074_ = lean_usize_land(v_x_1068_, v___x_1073_);
v_j_1075_ = lean_usize_to_nat(v___x_1074_);
v___x_1076_ = lean_array_get_size(v_es_1072_);
v___x_1077_ = lean_nat_dec_lt(v_j_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec(v_j_1075_);
lean_dec(v_x_1071_);
lean_dec(v_x_1070_);
return v_x_1067_;
}
else
{
lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1116_; 
lean_inc_ref(v_es_1072_);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v_x_1067_, 0);
lean_dec(v_unused_1117_);
v___x_1079_ = v_x_1067_;
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v_x_1067_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_v_1081_; lean_object* v___x_1082_; lean_object* v_xs_x27_1083_; lean_object* v___y_1085_; 
v_v_1081_ = lean_array_fget(v_es_1072_, v_j_1075_);
v___x_1082_ = lean_box(0);
v_xs_x27_1083_ = lean_array_fset(v_es_1072_, v_j_1075_, v___x_1082_);
switch(lean_obj_tag(v_v_1081_))
{
case 0:
{
lean_object* v_key_1090_; lean_object* v_val_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1101_; 
v_key_1090_ = lean_ctor_get(v_v_1081_, 0);
v_val_1091_ = lean_ctor_get(v_v_1081_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_v_1081_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1093_ = v_v_1081_;
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_val_1091_);
lean_inc(v_key_1090_);
lean_dec(v_v_1081_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_name_eq(v_x_1070_, v_key_1090_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1093_);
v___x_1096_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1090_, v_val_1091_, v_x_1070_, v_x_1071_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
v___y_1085_ = v___x_1097_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1099_; 
lean_dec(v_val_1091_);
lean_dec(v_key_1090_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_x_1071_);
lean_ctor_set(v___x_1093_, 0, v_x_1070_);
v___x_1099_ = v___x_1093_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_x_1070_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_x_1071_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
v___y_1085_ = v___x_1099_;
goto v___jp_1084_;
}
}
}
}
case 1:
{
lean_object* v_node_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1114_; 
v_node_1102_ = lean_ctor_get(v_v_1081_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_v_1081_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1104_ = v_v_1081_;
v_isShared_1105_ = v_isSharedCheck_1114_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_node_1102_);
lean_dec(v_v_1081_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1114_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1106_ = ((size_t)5ULL);
v___x_1107_ = lean_usize_shift_right(v_x_1068_, v___x_1106_);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_x_1069_, v___x_1108_);
v___x_1110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_node_1102_, v___x_1107_, v___x_1109_, v_x_1070_, v_x_1071_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1110_);
v___x_1112_ = v___x_1104_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v___y_1085_ = v___x_1112_;
goto v___jp_1084_;
}
}
}
default: 
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_x_1070_);
lean_ctor_set(v___x_1115_, 1, v_x_1071_);
v___y_1085_ = v___x_1115_;
goto v___jp_1084_;
}
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_array_fset(v_xs_x27_1083_, v_j_1075_, v___y_1085_);
lean_dec(v_j_1075_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1086_);
v___x_1088_ = v___x_1079_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
else
{
lean_object* v_ks_1118_; lean_object* v_vs_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1139_; 
v_ks_1118_ = lean_ctor_get(v_x_1067_, 0);
v_vs_1119_ = lean_ctor_get(v_x_1067_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1121_ = v_x_1067_;
v_isShared_1122_ = v_isSharedCheck_1139_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_vs_1119_);
lean_inc(v_ks_1118_);
lean_dec(v_x_1067_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1139_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_ks_1118_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_vs_1119_);
v___x_1124_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v_newNode_1125_; uint8_t v___y_1127_; size_t v___x_1133_; uint8_t v___x_1134_; 
v_newNode_1125_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v___x_1124_, v_x_1070_, v_x_1071_);
v___x_1133_ = ((size_t)7ULL);
v___x_1134_ = lean_usize_dec_le(v___x_1133_, v_x_1069_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1125_);
v___x_1136_ = lean_unsigned_to_nat(4u);
v___x_1137_ = lean_nat_dec_lt(v___x_1135_, v___x_1136_);
lean_dec(v___x_1135_);
v___y_1127_ = v___x_1137_;
goto v___jp_1126_;
}
else
{
v___y_1127_ = v___x_1134_;
goto v___jp_1126_;
}
v___jp_1126_:
{
if (v___y_1127_ == 0)
{
lean_object* v_ks_1128_; lean_object* v_vs_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_ks_1128_ = lean_ctor_get(v_newNode_1125_, 0);
lean_inc_ref(v_ks_1128_);
v_vs_1129_ = lean_ctor_get(v_newNode_1125_, 1);
lean_inc_ref(v_vs_1129_);
lean_dec_ref(v_newNode_1125_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0);
v___x_1132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_x_1069_, v_ks_1128_, v_vs_1129_, v___x_1130_, v___x_1131_);
lean_dec_ref(v_vs_1129_);
lean_dec_ref(v_ks_1128_);
return v___x_1132_;
}
else
{
return v_newNode_1125_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(size_t v_depth_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_i_1143_, lean_object* v_entries_1144_){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_keys_1141_);
v___x_1146_ = lean_nat_dec_lt(v_i_1143_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec(v_i_1143_);
return v_entries_1144_;
}
else
{
lean_object* v_k_1147_; lean_object* v_v_1148_; uint64_t v___y_1150_; 
v_k_1147_ = lean_array_fget_borrowed(v_keys_1141_, v_i_1143_);
v_v_1148_ = lean_array_fget_borrowed(v_vals_1142_, v_i_1143_);
if (lean_obj_tag(v_k_1147_) == 0)
{
uint64_t v___x_1161_; 
v___x_1161_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
v___y_1150_ = v___x_1161_;
goto v___jp_1149_;
}
else
{
uint64_t v_hash_1162_; 
v_hash_1162_ = lean_ctor_get_uint64(v_k_1147_, sizeof(void*)*2);
v___y_1150_ = v_hash_1162_;
goto v___jp_1149_;
}
v___jp_1149_:
{
size_t v_h_1151_; size_t v___x_1152_; lean_object* v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v_h_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_h_1151_ = lean_uint64_to_usize(v___y_1150_);
v___x_1152_ = ((size_t)5ULL);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_sub(v_depth_1140_, v___x_1154_);
v___x_1156_ = lean_usize_mul(v___x_1152_, v___x_1155_);
v_h_1157_ = lean_usize_shift_right(v_h_1151_, v___x_1156_);
v___x_1158_ = lean_nat_add(v_i_1143_, v___x_1153_);
lean_dec(v_i_1143_);
lean_inc(v_v_1148_);
lean_inc(v_k_1147_);
v___x_1159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_entries_1144_, v_h_1157_, v_depth_1140_, v_k_1147_, v_v_1148_);
v_i_1143_ = v___x_1158_;
v_entries_1144_ = v___x_1159_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___boxed(lean_object* v_depth_1163_, lean_object* v_keys_1164_, lean_object* v_vals_1165_, lean_object* v_i_1166_, lean_object* v_entries_1167_){
_start:
{
size_t v_depth_boxed_1168_; lean_object* v_res_1169_; 
v_depth_boxed_1168_ = lean_unbox_usize(v_depth_1163_);
lean_dec(v_depth_1163_);
v_res_1169_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_boxed_1168_, v_keys_1164_, v_vals_1165_, v_i_1166_, v_entries_1167_);
lean_dec_ref(v_vals_1165_);
lean_dec_ref(v_keys_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
size_t v_x_30268__boxed_1175_; size_t v_x_30269__boxed_1176_; lean_object* v_res_1177_; 
v_x_30268__boxed_1175_ = lean_unbox_usize(v_x_1171_);
lean_dec(v_x_1171_);
v_x_30269__boxed_1176_ = lean_unbox_usize(v_x_1172_);
lean_dec(v_x_1172_);
v_res_1177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1170_, v_x_30268__boxed_1175_, v_x_30269__boxed_1176_, v_x_1173_, v_x_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
uint64_t v___y_1182_; 
if (lean_obj_tag(v_x_1179_) == 0)
{
uint64_t v___x_1186_; 
v___x_1186_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
v___y_1182_ = v___x_1186_;
goto v___jp_1181_;
}
else
{
uint64_t v_hash_1187_; 
v_hash_1187_ = lean_ctor_get_uint64(v_x_1179_, sizeof(void*)*2);
v___y_1182_ = v_hash_1187_;
goto v___jp_1181_;
}
v___jp_1181_:
{
size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_uint64_to_usize(v___y_1182_);
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1178_, v___x_1183_, v___x_1184_, v_x_1179_, v_x_1180_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_keys_1188_, lean_object* v_vals_1189_, lean_object* v_i_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_array_get_size(v_keys_1188_);
v___x_1193_ = lean_nat_dec_lt(v_i_1190_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_i_1190_);
v___x_1194_ = lean_box(0);
return v___x_1194_;
}
else
{
lean_object* v_k_x27_1195_; uint8_t v___x_1196_; 
v_k_x27_1195_ = lean_array_fget_borrowed(v_keys_1188_, v_i_1190_);
v___x_1196_ = lean_name_eq(v_k_1191_, v_k_x27_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_add(v_i_1190_, v___x_1197_);
lean_dec(v_i_1190_);
v_i_1190_ = v___x_1198_;
goto _start;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_array_fget_borrowed(v_vals_1189_, v_i_1190_);
lean_dec(v_i_1190_);
lean_inc(v___x_1200_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1202_, lean_object* v_vals_1203_, lean_object* v_i_1204_, lean_object* v_k_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_1202_, v_vals_1203_, v_i_1204_, v_k_1205_);
lean_dec(v_k_1205_);
lean_dec_ref(v_vals_1203_);
lean_dec_ref(v_keys_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(lean_object* v_x_1207_, size_t v_x_1208_, lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_es_1210_; lean_object* v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v_j_1214_; lean_object* v___x_1215_; 
v_es_1210_ = lean_ctor_get(v_x_1207_, 0);
v___x_1211_ = lean_box(2);
v___x_1212_ = ((size_t)31ULL);
v___x_1213_ = lean_usize_land(v_x_1208_, v___x_1212_);
v_j_1214_ = lean_usize_to_nat(v___x_1213_);
v___x_1215_ = lean_array_get_borrowed(v___x_1211_, v_es_1210_, v_j_1214_);
lean_dec(v_j_1214_);
switch(lean_obj_tag(v___x_1215_))
{
case 0:
{
lean_object* v_key_1216_; lean_object* v_val_1217_; uint8_t v___x_1218_; 
v_key_1216_ = lean_ctor_get(v___x_1215_, 0);
v_val_1217_ = lean_ctor_get(v___x_1215_, 1);
v___x_1218_ = lean_name_eq(v_x_1209_, v_key_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_box(0);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; 
lean_inc(v_val_1217_);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_val_1217_);
return v___x_1220_;
}
}
case 1:
{
lean_object* v_node_1221_; size_t v___x_1222_; size_t v___x_1223_; 
v_node_1221_ = lean_ctor_get(v___x_1215_, 0);
v___x_1222_ = ((size_t)5ULL);
v___x_1223_ = lean_usize_shift_right(v_x_1208_, v___x_1222_);
v_x_1207_ = v_node_1221_;
v_x_1208_ = v___x_1223_;
goto _start;
}
default: 
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
}
}
else
{
lean_object* v_ks_1226_; lean_object* v_vs_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_ks_1226_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1227_ = lean_ctor_get(v_x_1207_, 1);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_ks_1226_, v_vs_1227_, v___x_1228_, v_x_1209_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_){
_start:
{
size_t v_x_30467__boxed_1233_; lean_object* v_res_1234_; 
v_x_30467__boxed_1233_ = lean_unbox_usize(v_x_1231_);
lean_dec(v_x_1231_);
v_res_1234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1230_, v_x_30467__boxed_1233_, v_x_1232_);
lean_dec(v_x_1232_);
lean_dec_ref(v_x_1230_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
uint64_t v___y_1238_; 
if (lean_obj_tag(v_x_1236_) == 0)
{
uint64_t v___x_1241_; 
v___x_1241_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
v___y_1238_ = v___x_1241_;
goto v___jp_1237_;
}
else
{
uint64_t v_hash_1242_; 
v_hash_1242_ = lean_ctor_get_uint64(v_x_1236_, sizeof(void*)*2);
v___y_1238_ = v_hash_1242_;
goto v___jp_1237_;
}
v___jp_1237_:
{
size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_uint64_to_usize(v___y_1238_);
v___x_1240_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1235_, v___x_1239_, v_x_1236_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg___boxed(lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_1243_, v_x_1244_);
lean_dec(v_x_1244_);
lean_dec_ref(v_x_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(lean_object* v_oldCounters_1246_, lean_object* v_x_1247_, lean_object* v_____s_1248_){
_start:
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1251_; 
v_fst_1249_ = lean_ctor_get(v_x_1247_, 0);
lean_inc(v_fst_1249_);
v_snd_1250_ = lean_ctor_get(v_x_1247_, 1);
lean_inc(v_snd_1250_);
lean_dec_ref(v_x_1247_);
v___x_1251_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_oldCounters_1246_, v_fst_1249_);
if (lean_obj_tag(v___x_1251_) == 1)
{
lean_object* v_val_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1261_; 
v_val_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_val_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v_result_1257_; lean_object* v___x_1259_; 
v___x_1256_ = lean_nat_sub(v_snd_1250_, v_val_1252_);
lean_dec(v_val_1252_);
lean_dec(v_snd_1250_);
v_result_1257_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_1248_, v_fst_1249_, v___x_1256_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v_result_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_result_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_result_1262_; lean_object* v___x_1263_; 
lean_dec(v___x_1251_);
v_result_1262_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_1248_, v_fst_1249_, v_snd_1250_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_result_1262_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed(lean_object* v_oldCounters_1264_, lean_object* v_x_1265_, lean_object* v_____s_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(v_oldCounters_1264_, v_x_1265_, v_____s_1266_);
lean_dec_ref(v_oldCounters_1264_);
return v_res_1267_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1269_; lean_object* v_result_1270_; 
v___x_1269_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0);
v_result_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_result_1270_, 0, v___x_1269_);
return v_result_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object* v_newCounters_1271_, lean_object* v_oldCounters_1272_){
_start:
{
lean_object* v___f_1273_; lean_object* v_result_1274_; lean_object* v___x_1275_; 
v___f_1273_ = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1273_, 0, v_oldCounters_1272_);
v_result_1274_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1);
v___x_1275_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_newCounters_1271_, v_result_1274_, v___f_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___boxed(lean_object* v_newCounters_1276_, lean_object* v_oldCounters_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_newCounters_1276_, v_oldCounters_1277_);
lean_dec_ref(v_newCounters_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(lean_object* v_f_1279_, lean_object* v_keys_1280_, lean_object* v_vals_1281_, lean_object* v_i_1282_, lean_object* v_acc_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v_keys_1280_);
v___x_1285_ = lean_nat_dec_lt(v_i_1282_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_i_1282_);
lean_dec(v_f_1279_);
return v_acc_1283_;
}
else
{
lean_object* v_k_1286_; lean_object* v_v_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_k_1286_ = lean_array_fget_borrowed(v_keys_1280_, v_i_1282_);
v_v_1287_ = lean_array_fget_borrowed(v_vals_1281_, v_i_1282_);
lean_inc(v_f_1279_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
v___x_1288_ = lean_apply_3(v_f_1279_, v_acc_1283_, v_k_1286_, v_v_1287_);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_add(v_i_1282_, v___x_1289_);
lean_dec(v_i_1282_);
v_i_1282_ = v___x_1290_;
v_acc_1283_ = v___x_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg___boxed(lean_object* v_f_1292_, lean_object* v_keys_1293_, lean_object* v_vals_1294_, lean_object* v_i_1295_, lean_object* v_acc_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_1292_, v_keys_1293_, v_vals_1294_, v_i_1295_, v_acc_1296_);
lean_dec_ref(v_vals_1294_);
lean_dec_ref(v_keys_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(lean_object* v_f_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
lean_object* v_es_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_es_1301_ = lean_ctor_get(v_x_1299_, 0);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_array_get_size(v_es_1301_);
v___x_1304_ = lean_nat_dec_lt(v___x_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_dec(v_f_1298_);
return v_x_1300_;
}
else
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_nat_dec_le(v___x_1303_, v___x_1303_);
if (v___x_1305_ == 0)
{
if (v___x_1304_ == 0)
{
lean_dec(v_f_1298_);
return v_x_1300_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1303_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_1298_, v_es_1301_, v___x_1306_, v___x_1307_, v_x_1300_);
return v___x_1308_;
}
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = lean_usize_of_nat(v___x_1303_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_1298_, v_es_1301_, v___x_1309_, v___x_1310_, v_x_1300_);
return v___x_1311_;
}
}
}
else
{
lean_object* v_ks_1312_; lean_object* v_vs_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_ks_1312_ = lean_ctor_get(v_x_1299_, 0);
v_vs_1313_ = lean_ctor_get(v_x_1299_, 1);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_1298_, v_ks_1312_, v_vs_1313_, v___x_1314_, v_x_1300_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(lean_object* v_f_1316_, lean_object* v_as_1317_, size_t v_i_1318_, size_t v_stop_1319_, lean_object* v_b_1320_){
_start:
{
lean_object* v___y_1322_; uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_eq(v_i_1318_, v_stop_1319_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_array_uget_borrowed(v_as_1317_, v_i_1318_);
switch(lean_obj_tag(v___x_1327_))
{
case 0:
{
lean_object* v_key_1328_; lean_object* v_val_1329_; lean_object* v___x_1330_; 
v_key_1328_ = lean_ctor_get(v___x_1327_, 0);
v_val_1329_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_f_1316_);
lean_inc(v_val_1329_);
lean_inc(v_key_1328_);
v___x_1330_ = lean_apply_3(v_f_1316_, v_b_1320_, v_key_1328_, v_val_1329_);
v___y_1322_ = v___x_1330_;
goto v___jp_1321_;
}
case 1:
{
lean_object* v_node_1331_; lean_object* v___x_1332_; 
v_node_1331_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_f_1316_);
v___x_1332_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1316_, v_node_1331_, v_b_1320_);
v___y_1322_ = v___x_1332_;
goto v___jp_1321_;
}
default: 
{
v___y_1322_ = v_b_1320_;
goto v___jp_1321_;
}
}
}
else
{
lean_dec(v_f_1316_);
return v_b_1320_;
}
v___jp_1321_:
{
size_t v___x_1323_; size_t v___x_1324_; 
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1318_, v___x_1323_);
v_i_1318_ = v___x_1324_;
v_b_1320_ = v___y_1322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg___boxed(lean_object* v_f_1333_, lean_object* v_as_1334_, lean_object* v_i_1335_, lean_object* v_stop_1336_, lean_object* v_b_1337_){
_start:
{
size_t v_i_boxed_1338_; size_t v_stop_boxed_1339_; lean_object* v_res_1340_; 
v_i_boxed_1338_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_stop_boxed_1339_ = lean_unbox_usize(v_stop_1336_);
lean_dec(v_stop_1336_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_1333_, v_as_1334_, v_i_boxed_1338_, v_stop_boxed_1339_, v_b_1337_);
lean_dec_ref(v_as_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg___boxed(lean_object* v_f_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1341_, v_x_1342_, v_x_1343_);
lean_dec_ref(v_x_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0(lean_object* v_f_1345_, lean_object* v_x1_1346_, lean_object* v_x2_1347_, lean_object* v_x3_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_apply_3(v_f_1345_, v_x1_1346_, v_x2_1347_, v_x3_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(lean_object* v_map_1350_, lean_object* v_f_1351_, lean_object* v_init_1352_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_1354_; 
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1353_, 0, v_f_1351_);
v___x_1354_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v___f_1353_, v_map_1350_, v_init_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___boxed(lean_object* v_map_1355_, lean_object* v_f_1356_, lean_object* v_init_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_1355_, v_f_1356_, v_init_1357_);
lean_dec_ref(v_map_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0(lean_object* v_ps_1359_, lean_object* v_k_1360_, lean_object* v_v_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_k_1360_);
lean_ctor_set(v___x_1362_, 1, v_v_1361_);
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v_ps_1359_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(lean_object* v_m_1365_){
_start:
{
lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___f_1366_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0));
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_m_1365_, v___f_1366_, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___boxed(lean_object* v_m_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_1369_);
lean_dec_ref(v_m_1369_);
return v_res_1370_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0));
v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2));
v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_box(1);
v___x_1378_ = l_Lean_MessageData_ofFormat(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5));
v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
return v___x_1381_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8));
v___x_1386_ = l_Lean_MessageData_ofFormat(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11));
v___x_1391_ = l_Lean_MessageData_ofFormat(v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1392_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(uint8_t v_a_1397_, lean_object* v_kind_1398_, lean_object* v___x_1399_, lean_object* v_a_1400_, uint8_t v___x_1401_, lean_object* v_diag_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___y_1409_; uint8_t v___y_1410_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; lean_object* v___x_1457_; lean_object* v_fileName_1458_; lean_object* v_fileMap_1459_; lean_object* v_options_1460_; lean_object* v_currRecDepth_1461_; lean_object* v_ref_1462_; lean_object* v_currNamespace_1463_; lean_object* v_openDecls_1464_; lean_object* v_initHeartbeats_1465_; lean_object* v_maxHeartbeats_1466_; lean_object* v_quotContext_1467_; lean_object* v_currMacroScope_1468_; lean_object* v_cancelTk_x3f_1469_; uint8_t v_suppressElabErrors_1470_; lean_object* v_inheritedTraceOptions_1471_; lean_object* v_env_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v_fileName_1477_; lean_object* v_fileMap_1478_; lean_object* v_currRecDepth_1479_; lean_object* v_ref_1480_; lean_object* v_currNamespace_1481_; lean_object* v_openDecls_1482_; lean_object* v_initHeartbeats_1483_; lean_object* v_maxHeartbeats_1484_; lean_object* v_quotContext_1485_; lean_object* v_currMacroScope_1486_; lean_object* v_cancelTk_x3f_1487_; uint8_t v_suppressElabErrors_1488_; lean_object* v_inheritedTraceOptions_1489_; lean_object* v___y_1490_; uint8_t v___y_1530_; uint8_t v___x_1552_; 
v___x_1457_ = lean_st_ref_get(v___y_1406_);
v_fileName_1458_ = lean_ctor_get(v___y_1405_, 0);
v_fileMap_1459_ = lean_ctor_get(v___y_1405_, 1);
v_options_1460_ = lean_ctor_get(v___y_1405_, 2);
v_currRecDepth_1461_ = lean_ctor_get(v___y_1405_, 3);
v_ref_1462_ = lean_ctor_get(v___y_1405_, 5);
v_currNamespace_1463_ = lean_ctor_get(v___y_1405_, 6);
v_openDecls_1464_ = lean_ctor_get(v___y_1405_, 7);
v_initHeartbeats_1465_ = lean_ctor_get(v___y_1405_, 8);
v_maxHeartbeats_1466_ = lean_ctor_get(v___y_1405_, 9);
v_quotContext_1467_ = lean_ctor_get(v___y_1405_, 10);
v_currMacroScope_1468_ = lean_ctor_get(v___y_1405_, 11);
v_cancelTk_x3f_1469_ = lean_ctor_get(v___y_1405_, 12);
v_suppressElabErrors_1470_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1471_ = lean_ctor_get(v___y_1405_, 13);
v_env_1472_ = lean_ctor_get(v___x_1457_, 0);
lean_inc_ref(v_env_1472_);
lean_dec(v___x_1457_);
v___x_1473_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1460_);
v___x_1474_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_options_1460_, v___x_1473_, v_a_1397_);
v___x_1475_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v___x_1474_, v___x_1473_);
v___x_1552_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1472_);
lean_dec_ref(v_env_1472_);
if (v___x_1552_ == 0)
{
if (v___x_1475_ == 0)
{
uint8_t v___x_1553_; 
v___x_1553_ = 1;
v___y_1530_ = v___x_1553_;
goto v___jp_1529_;
}
else
{
v___y_1530_ = v___x_1552_;
goto v___jp_1529_;
}
}
else
{
v___y_1530_ = v___x_1475_;
goto v___jp_1529_;
}
v___jp_1408_:
{
if (v___y_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v___y_1409_);
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1409_);
return v___x_1413_;
}
}
v___jp_1414_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1418_ = l_Lean_stringToMessageData(v_kind_1398_);
v___x_1419_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
lean_inc_ref(v___y_1417_);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v___y_1417_);
v___x_1422_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4);
v___x_1425_ = l_Lean_MessageData_joinSep(v___y_1415_, v___x_1424_);
v___x_1426_ = l_Lean_indentD(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1423_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Lean_Exception_toMessageData(v___y_1416_);
v___x_1431_ = l_Lean_indentD(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
v___jp_1435_:
{
if (v___y_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_diag_1442_; lean_object* v_unfoldCounter_1443_; lean_object* v_env_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1440_ = lean_st_ref_get(v___y_1404_);
v___x_1441_ = lean_st_ref_get(v___y_1436_);
v_diag_1442_ = lean_ctor_get(v___x_1440_, 4);
lean_inc_ref(v_diag_1442_);
lean_dec(v___x_1440_);
v_unfoldCounter_1443_ = lean_ctor_get(v_diag_1442_, 0);
lean_inc_ref(v_unfoldCounter_1443_);
lean_dec_ref(v_diag_1442_);
v_env_1444_ = lean_ctor_get(v___x_1441_, 0);
lean_inc_ref(v_env_1444_);
lean_dec(v___x_1441_);
v___x_1445_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v___y_1438_, v_unfoldCounter_1443_);
lean_dec_ref(v___y_1438_);
v___x_1446_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v___x_1445_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = lean_mk_empty_array_with_capacity(v___x_1399_);
v___x_1448_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(v_env_1444_, v___x_1446_, v___x_1447_);
v___x_1449_ = l_List_isEmpty___redArg(v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3));
v___x_1451_ = lean_string_dec_eq(v_kind_1398_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9);
v___y_1415_ = v___x_1448_;
v___y_1416_ = v___y_1437_;
v___y_1417_ = v___x_1452_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12);
v___y_1415_ = v___x_1448_;
v___y_1416_ = v___y_1437_;
v___y_1417_ = v___x_1453_;
goto v___jp_1414_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v___x_1448_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_kind_1398_);
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
else
{
lean_object* v___x_1456_; 
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_kind_1398_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1437_);
return v___x_1456_;
}
}
v___jp_1476_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = l_Lean_maxRecDepth;
v___x_1492_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v___x_1474_, v___x_1491_);
lean_inc_ref(v_inheritedTraceOptions_1489_);
lean_inc(v_cancelTk_x3f_1487_);
lean_inc(v_currMacroScope_1486_);
lean_inc(v_quotContext_1485_);
lean_inc(v_maxHeartbeats_1484_);
lean_inc(v_initHeartbeats_1483_);
lean_inc(v_openDecls_1482_);
lean_inc(v_currNamespace_1481_);
lean_inc(v_ref_1480_);
lean_inc(v_currRecDepth_1479_);
lean_inc_ref(v_fileMap_1478_);
lean_inc_ref(v_fileName_1477_);
v___x_1493_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1493_, 0, v_fileName_1477_);
lean_ctor_set(v___x_1493_, 1, v_fileMap_1478_);
lean_ctor_set(v___x_1493_, 2, v___x_1474_);
lean_ctor_set(v___x_1493_, 3, v_currRecDepth_1479_);
lean_ctor_set(v___x_1493_, 4, v___x_1492_);
lean_ctor_set(v___x_1493_, 5, v_ref_1480_);
lean_ctor_set(v___x_1493_, 6, v_currNamespace_1481_);
lean_ctor_set(v___x_1493_, 7, v_openDecls_1482_);
lean_ctor_set(v___x_1493_, 8, v_initHeartbeats_1483_);
lean_ctor_set(v___x_1493_, 9, v_maxHeartbeats_1484_);
lean_ctor_set(v___x_1493_, 10, v_quotContext_1485_);
lean_ctor_set(v___x_1493_, 11, v_currMacroScope_1486_);
lean_ctor_set(v___x_1493_, 12, v_cancelTk_x3f_1487_);
lean_ctor_set(v___x_1493_, 13, v_inheritedTraceOptions_1489_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*14, v___x_1475_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*14 + 1, v_suppressElabErrors_1488_);
lean_inc_ref(v_a_1400_);
v___x_1494_ = l_Lean_Meta_check(v_a_1400_, v___x_1401_, v___y_1403_, v___y_1404_, v___x_1493_, v___y_1490_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_mctx_1497_; lean_object* v_cache_1498_; lean_object* v_zetaDeltaFVarIds_1499_; lean_object* v_postponed_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref_known(v___x_1494_, 1);
v___x_1495_ = lean_st_ref_get(v___y_1404_);
v___x_1496_ = lean_st_ref_take(v___y_1404_);
v_mctx_1497_ = lean_ctor_get(v___x_1496_, 0);
v_cache_1498_ = lean_ctor_get(v___x_1496_, 1);
v_zetaDeltaFVarIds_1499_ = lean_ctor_get(v___x_1496_, 2);
v_postponed_1500_ = lean_ctor_get(v___x_1496_, 3);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v___x_1496_, 4);
lean_dec(v_unused_1525_);
v___x_1502_ = v___x_1496_;
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_postponed_1500_);
lean_inc(v_zetaDeltaFVarIds_1499_);
lean_inc(v_cache_1498_);
lean_inc(v_mctx_1497_);
lean_dec(v___x_1496_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v_diag_1402_);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_mctx_1497_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_cache_1498_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_zetaDeltaFVarIds_1499_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_postponed_1500_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_diag_1402_);
v___x_1505_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_st_ref_set(v___y_1404_, v___x_1505_);
v___x_1507_ = 5;
v___x_1508_ = l_Lean_Meta_check(v_a_1400_, v___x_1507_, v___y_1403_, v___y_1404_, v___x_1493_, v___y_1490_);
lean_dec_ref_known(v___x_1493_, 14);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v___x_1495_);
lean_dec_ref(v_kind_1398_);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v___x_1508_, 0);
lean_dec(v_unused_1517_);
v___x_1510_ = v___x_1508_;
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v___x_1508_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(0);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1512_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
lean_object* v_diag_1518_; lean_object* v_a_1519_; lean_object* v_unfoldCounter_1520_; uint8_t v___x_1521_; 
v_diag_1518_ = lean_ctor_get(v___x_1495_, 4);
lean_inc_ref(v_diag_1518_);
lean_dec(v___x_1495_);
v_a_1519_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1508_, 1);
v_unfoldCounter_1520_ = lean_ctor_get(v_diag_1518_, 0);
lean_inc_ref(v_unfoldCounter_1520_);
lean_dec_ref(v_diag_1518_);
v___x_1521_ = l_Lean_Exception_isInterrupt(v_a_1519_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
lean_inc(v_a_1519_);
v___x_1522_ = l_Lean_Exception_isRuntime(v_a_1519_);
v___y_1436_ = v___y_1490_;
v___y_1437_ = v_a_1519_;
v___y_1438_ = v_unfoldCounter_1520_;
v___y_1439_ = v___x_1522_;
goto v___jp_1435_;
}
else
{
v___y_1436_ = v___y_1490_;
v___y_1437_ = v_a_1519_;
v___y_1438_ = v_unfoldCounter_1520_;
v___y_1439_ = v___x_1521_;
goto v___jp_1435_;
}
}
}
}
}
else
{
lean_object* v_a_1526_; uint8_t v___x_1527_; 
lean_dec_ref_known(v___x_1493_, 14);
lean_dec_ref(v_diag_1402_);
lean_dec_ref(v_a_1400_);
lean_dec_ref(v_kind_1398_);
v_a_1526_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1527_ = l_Lean_Exception_isInterrupt(v_a_1526_);
if (v___x_1527_ == 0)
{
uint8_t v___x_1528_; 
lean_inc(v_a_1526_);
v___x_1528_ = l_Lean_Exception_isRuntime(v_a_1526_);
v___y_1409_ = v_a_1526_;
v___y_1410_ = v___x_1528_;
goto v___jp_1408_;
}
else
{
v___y_1409_ = v_a_1526_;
v___y_1410_ = v___x_1527_;
goto v___jp_1408_;
}
}
}
v___jp_1529_:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_bool_not(v___y_1530_);
if (v___x_1531_ == 0)
{
v_fileName_1477_ = v_fileName_1458_;
v_fileMap_1478_ = v_fileMap_1459_;
v_currRecDepth_1479_ = v_currRecDepth_1461_;
v_ref_1480_ = v_ref_1462_;
v_currNamespace_1481_ = v_currNamespace_1463_;
v_openDecls_1482_ = v_openDecls_1464_;
v_initHeartbeats_1483_ = v_initHeartbeats_1465_;
v_maxHeartbeats_1484_ = v_maxHeartbeats_1466_;
v_quotContext_1485_ = v_quotContext_1467_;
v_currMacroScope_1486_ = v_currMacroScope_1468_;
v_cancelTk_x3f_1487_ = v_cancelTk_x3f_1469_;
v_suppressElabErrors_1488_ = v_suppressElabErrors_1470_;
v_inheritedTraceOptions_1489_ = v_inheritedTraceOptions_1471_;
v___y_1490_ = v___y_1406_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1532_; lean_object* v_env_1533_; lean_object* v_nextMacroScope_1534_; lean_object* v_ngen_1535_; lean_object* v_auxDeclNGen_1536_; lean_object* v_traceState_1537_; lean_object* v_messages_1538_; lean_object* v_infoState_1539_; lean_object* v_snapshotTasks_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1550_; 
v___x_1532_ = lean_st_ref_take(v___y_1406_);
v_env_1533_ = lean_ctor_get(v___x_1532_, 0);
v_nextMacroScope_1534_ = lean_ctor_get(v___x_1532_, 1);
v_ngen_1535_ = lean_ctor_get(v___x_1532_, 2);
v_auxDeclNGen_1536_ = lean_ctor_get(v___x_1532_, 3);
v_traceState_1537_ = lean_ctor_get(v___x_1532_, 4);
v_messages_1538_ = lean_ctor_get(v___x_1532_, 6);
v_infoState_1539_ = lean_ctor_get(v___x_1532_, 7);
v_snapshotTasks_1540_ = lean_ctor_get(v___x_1532_, 8);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1532_, 5);
lean_dec(v_unused_1551_);
v___x_1542_ = v___x_1532_;
v_isShared_1543_ = v_isSharedCheck_1550_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_snapshotTasks_1540_);
lean_inc(v_infoState_1539_);
lean_inc(v_messages_1538_);
lean_inc(v_traceState_1537_);
lean_inc(v_auxDeclNGen_1536_);
lean_inc(v_ngen_1535_);
lean_inc(v_nextMacroScope_1534_);
lean_inc(v_env_1533_);
lean_dec(v___x_1532_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1550_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = l_Lean_Kernel_enableDiag(v_env_1533_, v___x_1475_);
v___x_1545_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 5, v___x_1545_);
lean_ctor_set(v___x_1542_, 0, v___x_1544_);
v___x_1547_ = v___x_1542_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_nextMacroScope_1534_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_ngen_1535_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_auxDeclNGen_1536_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_traceState_1537_);
lean_ctor_set(v_reuseFailAlloc_1549_, 5, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1549_, 6, v_messages_1538_);
lean_ctor_set(v_reuseFailAlloc_1549_, 7, v_infoState_1539_);
lean_ctor_set(v_reuseFailAlloc_1549_, 8, v_snapshotTasks_1540_);
v___x_1547_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_st_ref_set(v___y_1406_, v___x_1547_);
v_fileName_1477_ = v_fileName_1458_;
v_fileMap_1478_ = v_fileMap_1459_;
v_currRecDepth_1479_ = v_currRecDepth_1461_;
v_ref_1480_ = v_ref_1462_;
v_currNamespace_1481_ = v_currNamespace_1463_;
v_openDecls_1482_ = v_openDecls_1464_;
v_initHeartbeats_1483_ = v_initHeartbeats_1465_;
v_maxHeartbeats_1484_ = v_maxHeartbeats_1466_;
v_quotContext_1485_ = v_quotContext_1467_;
v_currMacroScope_1486_ = v_currMacroScope_1468_;
v_cancelTk_x3f_1487_ = v_cancelTk_x3f_1469_;
v_suppressElabErrors_1488_ = v_suppressElabErrors_1470_;
v_inheritedTraceOptions_1489_ = v_inheritedTraceOptions_1471_;
v___y_1490_ = v___y_1406_;
goto v___jp_1476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed(lean_object* v_a_1554_, lean_object* v_kind_1555_, lean_object* v___x_1556_, lean_object* v_a_1557_, lean_object* v___x_1558_, lean_object* v_diag_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v_a_30726__boxed_1565_; uint8_t v___x_30729__boxed_1566_; lean_object* v_res_1567_; 
v_a_30726__boxed_1565_ = lean_unbox(v_a_1554_);
v___x_30729__boxed_1566_ = lean_unbox(v___x_1558_);
v_res_1567_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(v_a_30726__boxed_1565_, v_kind_1555_, v___x_1556_, v_a_1557_, v___x_30729__boxed_1566_, v_diag_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___x_1556_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(uint8_t v_a_1573_, lean_object* v_kind_1574_, lean_object* v_as_x27_1575_, lean_object* v_b_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
if (lean_obj_tag(v_as_x27_1575_) == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v_kind_1574_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_b_1576_);
return v___x_1582_;
}
else
{
lean_object* v_head_1583_; lean_object* v_tail_1584_; lean_object* v___x_1585_; lean_object* v_mctx_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_a_1590_; lean_object* v___x_1595_; 
lean_dec_ref(v_b_1576_);
v_head_1583_ = lean_ctor_get(v_as_x27_1575_, 0);
v_tail_1584_ = lean_ctor_get(v_as_x27_1575_, 1);
v___x_1585_ = lean_st_ref_get(v___y_1578_);
v_mctx_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_mctx_1586_);
lean_dec(v___x_1585_);
v___x_1587_ = lean_box(0);
v___x_1588_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0));
v___x_1595_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1586_, v_head_1583_);
lean_dec_ref(v_mctx_1586_);
if (lean_obj_tag(v___x_1595_) == 1)
{
lean_object* v_val_1596_; lean_object* v_lctx_1597_; lean_object* v_type_1598_; lean_object* v___x_1599_; lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v_diag_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; 
v_val_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v_lctx_1597_ = lean_ctor_get(v_val_1596_, 1);
lean_inc_ref(v_lctx_1597_);
v_type_1598_ = lean_ctor_get(v_val_1596_, 2);
lean_inc_ref(v_type_1598_);
lean_dec(v_val_1596_);
v___x_1599_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_1598_, v___y_1578_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = lean_st_ref_get(v___y_1578_);
v_diag_1602_ = lean_ctor_get(v___x_1601_, 4);
lean_inc_ref_n(v_diag_1602_, 2);
lean_dec(v___x_1601_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1));
v___x_1605_ = 1;
v___x_1606_ = lean_box(v_a_1573_);
v___x_1607_ = lean_box(v___x_1605_);
lean_inc_ref(v_kind_1574_);
v___f_1608_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1608_, 0, v___x_1606_);
lean_closure_set(v___f_1608_, 1, v_kind_1574_);
lean_closure_set(v___f_1608_, 2, v___x_1603_);
lean_closure_set(v___f_1608_, 3, v_a_1600_);
lean_closure_set(v___f_1608_, 4, v___x_1607_);
lean_closure_set(v___f_1608_, 5, v_diag_1602_);
v___x_1609_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_1597_, v___x_1604_, v___f_1608_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v_mctx_1612_; lean_object* v_cache_1613_; lean_object* v_zetaDeltaFVarIds_1614_; lean_object* v_postponed_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = lean_st_ref_take(v___y_1578_);
v_mctx_1612_ = lean_ctor_get(v___x_1611_, 0);
v_cache_1613_ = lean_ctor_get(v___x_1611_, 1);
v_zetaDeltaFVarIds_1614_ = lean_ctor_get(v___x_1611_, 2);
v_postponed_1615_ = lean_ctor_get(v___x_1611_, 3);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1611_, 4);
lean_dec(v_unused_1624_);
v___x_1617_ = v___x_1611_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_postponed_1615_);
lean_inc(v_zetaDeltaFVarIds_1614_);
lean_inc(v_cache_1613_);
lean_inc(v_mctx_1612_);
lean_dec(v___x_1611_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 4, v_diag_1602_);
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_mctx_1612_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_cache_1613_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_zetaDeltaFVarIds_1614_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_postponed_1615_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_diag_1602_);
v___x_1620_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_st_ref_set(v___y_1578_, v___x_1620_);
v_a_1590_ = v_a_1610_;
goto v___jp_1589_;
}
}
}
else
{
lean_dec_ref(v_diag_1602_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1625_; 
v_a_1625_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1609_, 1);
v_a_1590_ = v_a_1625_;
goto v___jp_1589_;
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_kind_1574_);
v_a_1626_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1609_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1609_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
else
{
lean_dec(v___x_1595_);
v_as_x27_1575_ = v_tail_1584_;
v_b_1576_ = v___x_1588_;
goto _start;
}
v___jp_1589_:
{
if (lean_obj_tag(v_a_1590_) == 1)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v_kind_1574_);
v___x_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_a_1590_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v___x_1587_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
else
{
lean_dec(v_a_1590_);
v_as_x27_1575_ = v_tail_1584_;
v_b_1576_ = v___x_1588_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___boxed(lean_object* v_a_1635_, lean_object* v_kind_1636_, lean_object* v_as_x27_1637_, lean_object* v_b_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v_a_30993__boxed_1644_; lean_object* v_res_1645_; 
v_a_30993__boxed_1644_ = lean_unbox(v_a_1635_);
v_res_1645_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_30993__boxed_1644_, v_kind_1636_, v_as_x27_1637_, v_b_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v_as_x27_1637_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(uint8_t v_a_1646_, lean_object* v_kind_1647_, lean_object* v_goals_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0));
v___x_1656_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_1646_, v_kind_1647_, v_goals_1648_, v___x_1655_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1669_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1669_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1669_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_fst_1661_; 
v_fst_1661_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_fst_1661_);
lean_dec(v_a_1657_);
if (lean_obj_tag(v_fst_1661_) == 0)
{
lean_object* v___x_1663_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1654_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1654_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1667_; 
v_val_1665_ = lean_ctor_get(v_fst_1661_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v_fst_1661_, 1);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v_val_1665_);
v___x_1667_ = v___x_1659_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_val_1665_);
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
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1656_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1656_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed(lean_object* v_a_1678_, lean_object* v_kind_1679_, lean_object* v_goals_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v_a_31111__boxed_1686_; lean_object* v_res_1687_; 
v_a_31111__boxed_1686_ = lean_unbox(v_a_1678_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(v_a_31111__boxed_1686_, v_kind_1679_, v_goals_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_goals_1680_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(uint8_t v_a_1688_, lean_object* v_val_1689_, lean_object* v_as_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v_val_1689_);
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_b_1693_);
return v___x_1698_;
}
else
{
lean_object* v___x_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___f_1705_; lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1699_ = lean_box(v_a_1688_);
v___f_1700_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1700_, 0, v___x_1699_);
v___x_1701_ = lean_box(v_a_1688_);
v___f_1702_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1702_, 0, v___x_1701_);
v___x_1703_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1704_ = lean_box(v_a_1688_);
lean_inc(v_val_1689_);
v___f_1705_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1705_, 0, v_val_1689_);
lean_closure_set(v___f_1705_, 1, v___x_1704_);
lean_closure_set(v___f_1705_, 2, v___x_1703_);
lean_closure_set(v___f_1705_, 3, v___f_1700_);
v_a_1706_ = lean_array_uget_borrowed(v_as_1690_, v_i_1692_);
v___x_1707_ = lean_box(0);
lean_inc(v_a_1706_);
v___x_1708_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___f_1702_, v___f_1705_, v___x_1707_, v_a_1706_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; 
lean_dec_ref_known(v___x_1708_, 1);
v___x_1709_ = lean_box(0);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1692_, v___x_1710_);
v_i_1692_ = v___x_1711_;
v_b_1693_ = v___x_1709_;
goto _start;
}
else
{
lean_dec(v_val_1689_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___boxed(lean_object* v_a_1713_, lean_object* v_val_1714_, lean_object* v_as_1715_, lean_object* v_sz_1716_, lean_object* v_i_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_a_31176__boxed_1722_; size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_a_31176__boxed_1722_ = lean_unbox(v_a_1713_);
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1716_);
lean_dec(v_sz_1716_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v_a_31176__boxed_1722_, v_val_1714_, v_as_1715_, v_sz_boxed_1723_, v_i_boxed_1724_, v_b_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_as_1715_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object* v___cmdStx_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1761_; 
v___x_1730_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1731_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_1730_, v___y_1728_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1761_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1761_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_unbox(v_a_1732_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_dec(v_a_1732_);
v___x_1737_ = lean_box(0);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1737_);
v___x_1739_ = v___x_1734_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v_infoState_1745_; lean_object* v_trees_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; size_t v_sz_1749_; size_t v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
lean_del_object(v___x_1734_);
v___x_1741_ = lean_st_ref_get(v___y_1728_);
v___x_1742_ = 0;
v___x_1743_ = lean_box(v___x_1742_);
v___x_1744_ = lean_st_mk_ref(v___x_1743_);
v_infoState_1745_ = lean_ctor_get(v___x_1741_, 8);
lean_inc_ref(v_infoState_1745_);
lean_dec(v___x_1741_);
v_trees_1746_ = lean_ctor_get(v_infoState_1745_, 2);
lean_inc_ref(v_trees_1746_);
lean_dec_ref(v_infoState_1745_);
v___x_1747_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1746_);
lean_dec_ref(v_trees_1746_);
v___x_1748_ = lean_box(0);
v_sz_1749_ = lean_array_size(v___x_1747_);
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = lean_unbox(v_a_1732_);
lean_dec(v_a_1732_);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v___x_1751_, v___x_1744_, v___x_1747_, v_sz_1749_, v___x_1750_, v___x_1748_, v___y_1727_, v___y_1728_);
lean_dec_ref(v___x_1747_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1752_, 0);
lean_dec(v_unused_1760_);
v___x_1754_ = v___x_1752_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_dec(v___x_1752_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1748_);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1748_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object* v___cmdStx_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(v___cmdStx_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___cmdStx_1762_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object* v_opt_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1775_, v___y_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object* v_opt_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v_opt_1780_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object* v_00_u03b2_1785_, lean_object* v_m_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object* v_00_u03b2_1788_, lean_object* v_m_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_00_u03b2_1788_, v_m_1789_);
lean_dec_ref(v_m_1789_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(uint8_t v_a_1791_, lean_object* v_kind_1792_, lean_object* v_as_1793_, lean_object* v_as_x27_1794_, lean_object* v_b_1795_, lean_object* v_a_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_1791_, v_kind_1792_, v_as_x27_1794_, v_b_1795_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object* v_a_1803_, lean_object* v_kind_1804_, lean_object* v_as_1805_, lean_object* v_as_x27_1806_, lean_object* v_b_1807_, lean_object* v_a_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_a_31355__boxed_1814_; lean_object* v_res_1815_; 
v_a_31355__boxed_1814_ = lean_unbox(v_a_1803_);
v_res_1815_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_a_31355__boxed_1814_, v_kind_1804_, v_as_1805_, v_as_x27_1806_, v_b_1807_, v_a_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_as_x27_1806_);
lean_dec(v_as_1805_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(lean_object* v_00_u03b2_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_1817_, v_x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(v_00_u03b2_1820_, v_x_1821_, v_x_1822_);
lean_dec(v_x_1822_);
lean_dec_ref(v_x_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7(lean_object* v_00_u03b2_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_x_1825_, v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(lean_object* v_00_u03c3_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_map_1831_, lean_object* v_init_1832_, lean_object* v_f_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_1831_, v_init_1832_, v_f_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1835_, lean_object* v_00_u03b2_1836_, lean_object* v_map_1837_, lean_object* v_init_1838_, lean_object* v_f_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(v_00_u03c3_1835_, v_00_u03b2_1836_, v_map_1837_, v_init_1838_, v_f_1839_);
lean_dec_ref(v_map_1837_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(lean_object* v_00_u03c3_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_map_1843_, lean_object* v_f_1844_, lean_object* v_init_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_1843_, v_f_1844_, v_init_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___boxed(lean_object* v_00_u03c3_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_map_1849_, lean_object* v_f_1850_, lean_object* v_init_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(v_00_u03c3_1847_, v_00_u03b2_1848_, v_map_1849_, v_f_1850_, v_init_1851_);
lean_dec_ref(v_map_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(lean_object* v_00_u03b1_1853_, lean_object* v_msg_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(v_00_u03b1_1859_, v_msg_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(lean_object* v_00_u03b1_1865_, lean_object* v_preNode_1866_, lean_object* v_postNode_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_1866_, v_postNode_1867_, v_x_1868_, v_x_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_preNode_1875_, lean_object* v_postNode_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(v_00_u03b1_1874_, v_preNode_1875_, v_postNode_1876_, v_x_1877_, v_x_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1883_, lean_object* v_x_1884_, size_t v_x_1885_, lean_object* v_x_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1884_, v_x_1885_, v_x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
size_t v_x_31427__boxed_1892_; lean_object* v_res_1893_; 
v_x_31427__boxed_1892_ = lean_unbox_usize(v_x_1890_);
lean_dec(v_x_1890_);
v_res_1893_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(v_00_u03b2_1888_, v_x_1889_, v_x_31427__boxed_1892_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec_ref(v_x_1889_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_1894_, lean_object* v_x_1895_, size_t v_x_1896_, size_t v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1895_, v_x_1896_, v_x_1897_, v_x_1898_, v_x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
size_t v_x_31438__boxed_1907_; size_t v_x_31439__boxed_1908_; lean_object* v_res_1909_; 
v_x_31438__boxed_1907_ = lean_unbox_usize(v_x_1903_);
lean_dec(v_x_1903_);
v_x_31439__boxed_1908_ = lean_unbox_usize(v_x_1904_);
lean_dec(v_x_1904_);
v_res_1909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(v_00_u03b2_1901_, v_x_1902_, v_x_31438__boxed_1907_, v_x_31439__boxed_1908_, v_x_1905_, v_x_1906_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12___redArg(lean_object* v_map_1910_, lean_object* v_f_1911_, lean_object* v_init_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_1911_, v_map_1910_, v_init_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12(lean_object* v_00_u03c3_1914_, lean_object* v_00_u03c3_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_map_1917_, lean_object* v_f_1918_, lean_object* v_init_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_1918_, v_map_1917_, v_init_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(lean_object* v_map_1921_, lean_object* v_f_1922_, lean_object* v_init_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1922_, v_map_1921_, v_init_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_map_1925_, lean_object* v_f_1926_, lean_object* v_init_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(v_map_1925_, v_f_1926_, v_init_1927_);
lean_dec_ref(v_map_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(lean_object* v_00_u03c3_1929_, lean_object* v_00_u03b2_1930_, lean_object* v_map_1931_, lean_object* v_f_1932_, lean_object* v_init_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1932_, v_map_1931_, v_init_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03c3_1935_, lean_object* v_00_u03b2_1936_, lean_object* v_map_1937_, lean_object* v_f_1938_, lean_object* v_init_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(v_00_u03c3_1935_, v_00_u03b2_1936_, v_map_1937_, v_f_1938_, v_init_1939_);
lean_dec_ref(v_map_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(lean_object* v_msgData_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_1941_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___boxed(lean_object* v_msgData_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(v_msgData_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(lean_object* v_00_u03b1_1951_, lean_object* v_preNode_1952_, lean_object* v_postNode_1953_, lean_object* v___x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_1952_, v_postNode_1953_, v___x_1954_, v_x_1955_, v_x_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_preNode_1962_, lean_object* v_postNode_1963_, lean_object* v___x_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(v_00_u03b1_1961_, v_preNode_1962_, v_postNode_1963_, v___x_1964_, v_x_1965_, v_x_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b2_1971_, lean_object* v_keys_1972_, lean_object* v_vals_1973_, lean_object* v_heq_1974_, lean_object* v_i_1975_, lean_object* v_k_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_1972_, v_vals_1973_, v_i_1975_, v_k_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b2_1978_, lean_object* v_keys_1979_, lean_object* v_vals_1980_, lean_object* v_heq_1981_, lean_object* v_i_1982_, lean_object* v_k_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(v_00_u03b2_1978_, v_keys_1979_, v_vals_1980_, v_heq_1981_, v_i_1982_, v_k_1983_);
lean_dec(v_k_1983_);
lean_dec_ref(v_vals_1980_);
lean_dec_ref(v_keys_1979_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18(lean_object* v_00_u03b2_1985_, lean_object* v_n_1986_, lean_object* v_k_1987_, lean_object* v_v_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v_n_1986_, v_k_1987_, v_v_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(lean_object* v_00_u03b2_1990_, size_t v_depth_1991_, lean_object* v_keys_1992_, lean_object* v_vals_1993_, lean_object* v_heq_1994_, lean_object* v_i_1995_, lean_object* v_entries_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_1991_, v_keys_1992_, v_vals_1993_, v_i_1995_, v_entries_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___boxed(lean_object* v_00_u03b2_1998_, lean_object* v_depth_1999_, lean_object* v_keys_2000_, lean_object* v_vals_2001_, lean_object* v_heq_2002_, lean_object* v_i_2003_, lean_object* v_entries_2004_){
_start:
{
size_t v_depth_boxed_2005_; lean_object* v_res_2006_; 
v_depth_boxed_2005_ = lean_unbox_usize(v_depth_1999_);
lean_dec(v_depth_1999_);
v_res_2006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(v_00_u03b2_1998_, v_depth_boxed_2005_, v_keys_2000_, v_vals_2001_, v_heq_2002_, v_i_2003_, v_entries_2004_);
lean_dec_ref(v_vals_2001_);
lean_dec_ref(v_keys_2000_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22(lean_object* v_00_u03c3_2007_, lean_object* v_00_u03c3_2008_, lean_object* v_00_u03b1_2009_, lean_object* v_00_u03b2_2010_, lean_object* v_f_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_2011_, v_x_2012_, v_x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(lean_object* v_00_u03c3_2015_, lean_object* v_00_u03b1_2016_, lean_object* v_00_u03b2_2017_, lean_object* v_f_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_2018_, v_x_2019_, v_x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___boxed(lean_object* v_00_u03c3_2022_, lean_object* v_00_u03b1_2023_, lean_object* v_00_u03b2_2024_, lean_object* v_f_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(v_00_u03c3_2022_, v_00_u03b1_2023_, v_00_u03b2_2024_, v_f_2025_, v_x_2026_, v_x_2027_);
lean_dec_ref(v_x_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_x_2030_, v_x_2031_, v_x_2032_, v_x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(lean_object* v_00_u03b1_2035_, lean_object* v_00_u03b2_2036_, lean_object* v_00_u03c3_2037_, lean_object* v_00_u03c3_2038_, lean_object* v_f_2039_, lean_object* v_as_2040_, size_t v_i_2041_, size_t v_stop_2042_, lean_object* v_b_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_2039_, v_as_2040_, v_i_2041_, v_stop_2042_, v_b_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_00_u03c3_2047_, lean_object* v_00_u03c3_2048_, lean_object* v_f_2049_, lean_object* v_as_2050_, lean_object* v_i_2051_, lean_object* v_stop_2052_, lean_object* v_b_2053_){
_start:
{
size_t v_i_boxed_2054_; size_t v_stop_boxed_2055_; lean_object* v_res_2056_; 
v_i_boxed_2054_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_stop_boxed_2055_ = lean_unbox_usize(v_stop_2052_);
lean_dec(v_stop_2052_);
v_res_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(v_00_u03b1_2045_, v_00_u03b2_2046_, v_00_u03c3_2047_, v_00_u03c3_2048_, v_f_2049_, v_as_2050_, v_i_boxed_2054_, v_stop_boxed_2055_, v_b_2053_);
lean_dec_ref(v_as_2050_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(lean_object* v_00_u03c3_2057_, lean_object* v_00_u03c3_2058_, lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_f_2061_, lean_object* v_keys_2062_, lean_object* v_vals_2063_, lean_object* v_heq_2064_, lean_object* v_i_2065_, lean_object* v_acc_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_2061_, v_keys_2062_, v_vals_2063_, v_i_2065_, v_acc_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___boxed(lean_object* v_00_u03c3_2068_, lean_object* v_00_u03c3_2069_, lean_object* v_00_u03b1_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_f_2072_, lean_object* v_keys_2073_, lean_object* v_vals_2074_, lean_object* v_heq_2075_, lean_object* v_i_2076_, lean_object* v_acc_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(v_00_u03c3_2068_, v_00_u03c3_2069_, v_00_u03b1_2070_, v_00_u03b2_2071_, v_f_2072_, v_keys_2073_, v_vals_2074_, v_heq_2075_, v_i_2076_, v_acc_2077_);
lean_dec_ref(v_vals_2074_);
lean_dec_ref(v_keys_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(lean_object* v_00_u03b1_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_00_u03c3_2081_, lean_object* v_f_2082_, lean_object* v_as_2083_, size_t v_i_2084_, size_t v_stop_2085_, lean_object* v_b_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_2082_, v_as_2083_, v_i_2084_, v_stop_2085_, v_b_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___boxed(lean_object* v_00_u03b1_2088_, lean_object* v_00_u03b2_2089_, lean_object* v_00_u03c3_2090_, lean_object* v_f_2091_, lean_object* v_as_2092_, lean_object* v_i_2093_, lean_object* v_stop_2094_, lean_object* v_b_2095_){
_start:
{
size_t v_i_boxed_2096_; size_t v_stop_boxed_2097_; lean_object* v_res_2098_; 
v_i_boxed_2096_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_stop_boxed_2097_ = lean_unbox_usize(v_stop_2094_);
lean_dec(v_stop_2094_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(v_00_u03b1_2088_, v_00_u03b2_2089_, v_00_u03c3_2090_, v_f_2091_, v_as_2092_, v_i_boxed_2096_, v_stop_boxed_2097_, v_b_2095_);
lean_dec_ref(v_as_2092_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(lean_object* v_00_u03c3_2099_, lean_object* v_00_u03b1_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_f_2102_, lean_object* v_keys_2103_, lean_object* v_vals_2104_, lean_object* v_heq_2105_, lean_object* v_i_2106_, lean_object* v_acc_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_2102_, v_keys_2103_, v_vals_2104_, v_i_2106_, v_acc_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2109_, lean_object* v_00_u03b1_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_f_2112_, lean_object* v_keys_2113_, lean_object* v_vals_2114_, lean_object* v_heq_2115_, lean_object* v_i_2116_, lean_object* v_acc_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(v_00_u03c3_2109_, v_00_u03b1_2110_, v_00_u03b2_2111_, v_f_2112_, v_keys_2113_, v_vals_2114_, v_heq_2115_, v_i_2116_, v_acc_2117_);
lean_dec_ref(v_vals_2114_);
lean_dec_ref(v_keys_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances));
v___x_2121_ = l_Lean_Elab_Command_addLinter(v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
return v_res_2123_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Diagnostics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_TacticTypeCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
