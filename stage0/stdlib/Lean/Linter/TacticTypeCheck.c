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
v___x_103_ = lean_st_ref_set(v___y_84_, v___x_102_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(lean_object* v_opts_126_, lean_object* v_opt_127_){
_start:
{
lean_object* v_name_128_; lean_object* v_defValue_129_; lean_object* v_map_130_; lean_object* v___x_131_; 
v_name_128_ = lean_ctor_get(v_opt_127_, 0);
v_defValue_129_ = lean_ctor_get(v_opt_127_, 1);
v_map_130_ = lean_ctor_get(v_opts_126_, 0);
v___x_131_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_130_, v_name_128_);
if (lean_obj_tag(v___x_131_) == 0)
{
uint8_t v___x_132_; 
v___x_132_ = lean_unbox(v_defValue_129_);
return v___x_132_;
}
else
{
lean_object* v_val_133_; 
v_val_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v___x_131_, 1);
if (lean_obj_tag(v_val_133_) == 1)
{
uint8_t v_v_134_; 
v_v_134_ = lean_ctor_get_uint8(v_val_133_, 0);
lean_dec_ref_known(v_val_133_, 0);
return v_v_134_;
}
else
{
uint8_t v___x_135_; 
lean_dec(v_val_133_);
v___x_135_ = lean_unbox(v_defValue_129_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3___boxed(lean_object* v_opts_136_, lean_object* v_opt_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_136_, v_opt_137_);
lean_dec_ref(v_opt_137_);
lean_dec_ref(v_opts_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(lean_object* v_opts_140_, lean_object* v_opt_141_){
_start:
{
lean_object* v_name_142_; lean_object* v_defValue_143_; lean_object* v_map_144_; lean_object* v___x_145_; 
v_name_142_ = lean_ctor_get(v_opt_141_, 0);
v_defValue_143_ = lean_ctor_get(v_opt_141_, 1);
v_map_144_ = lean_ctor_get(v_opts_140_, 0);
v___x_145_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_144_, v_name_142_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_inc(v_defValue_143_);
return v_defValue_143_;
}
else
{
lean_object* v_val_146_; 
v_val_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_146_);
lean_dec_ref_known(v___x_145_, 1);
if (lean_obj_tag(v_val_146_) == 3)
{
lean_object* v_v_147_; 
v_v_147_ = lean_ctor_get(v_val_146_, 0);
lean_inc(v_v_147_);
lean_dec_ref_known(v_val_146_, 1);
return v_v_147_;
}
else
{
lean_dec(v_val_146_);
lean_inc(v_defValue_143_);
return v_defValue_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4___boxed(lean_object* v_opts_148_, lean_object* v_opt_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v_opts_148_, v_opt_149_);
lean_dec_ref(v_opt_149_);
lean_dec_ref(v_opts_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(lean_object* v_lctx_151_, lean_object* v_localInsts_152_, lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_151_, v_localInsts_152_, v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_159_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_159_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg___boxed(lean_object* v_lctx_176_, lean_object* v_localInsts_177_, lean_object* v_x_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_176_, v_localInsts_177_, v_x_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(lean_object* v_00_u03b1_185_, lean_object* v_lctx_186_, lean_object* v_localInsts_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_186_, v_localInsts_187_, v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___boxed(lean_object* v_00_u03b1_195_, lean_object* v_lctx_196_, lean_object* v_localInsts_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8(v_00_u03b1_195_, v_lctx_196_, v_localInsts_197_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(lean_object* v_opt_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_scopes_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_opts_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_208_ = lean_st_ref_get(v___y_206_);
v_scopes_209_ = lean_ctor_get(v___x_208_, 2);
lean_inc(v_scopes_209_);
lean_dec(v___x_208_);
v___x_210_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_211_ = l_List_head_x21___redArg(v___x_210_, v_scopes_209_);
lean_dec(v_scopes_209_);
v_opts_212_ = lean_ctor_get(v___x_211_, 1);
lean_inc_ref(v_opts_212_);
lean_dec(v___x_211_);
v___x_213_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_212_, v_opt_205_);
lean_dec_ref(v_opts_212_);
v___x_214_ = lean_box(v___x_213_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg___boxed(lean_object* v_opt_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v_opt_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(uint8_t v_a_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_box(v_a_220_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed(lean_object* v_a_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
uint8_t v_a_28989__boxed_236_; lean_object* v_res_237_; 
v_a_28989__boxed_236_ = lean_unbox(v_a_229_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(v_a_28989__boxed_236_, v_x_230_, v_x_231_, v_x_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec_ref(v_x_232_);
lean_dec_ref(v_x_231_);
lean_dec_ref(v_x_230_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(lean_object* v_postNode_238_, lean_object* v_ci_239_, lean_object* v_i_240_, lean_object* v_cs_241_, lean_object* v_x_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; 
lean_inc(v___y_244_);
lean_inc_ref(v___y_243_);
v___x_246_ = lean_apply_6(v_postNode_238_, v_ci_239_, v_i_240_, v_cs_241_, v___y_243_, v___y_244_, lean_box(0));
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed(lean_object* v_postNode_247_, lean_object* v_ci_248_, lean_object* v_i_249_, lean_object* v_cs_250_, lean_object* v_x_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0(v_postNode_247_, v_ci_248_, v_i_249_, v_cs_250_, v_x_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v_x_251_);
return v_res_255_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_instMonadEIO(lean_box(0));
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(lean_object* v_msg_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_toApplicative_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_296_; 
v___x_263_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__0);
v___x_264_ = l_StateRefT_x27_instMonad___redArg(v___x_263_);
v_toApplicative_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_264_, 1);
lean_dec(v_unused_297_);
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_296_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_toApplicative_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_296_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_toFunctor_269_; lean_object* v_toSeq_270_; lean_object* v_toSeqLeft_271_; lean_object* v_toSeqRight_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_294_; 
v_toFunctor_269_ = lean_ctor_get(v_toApplicative_265_, 0);
v_toSeq_270_ = lean_ctor_get(v_toApplicative_265_, 2);
v_toSeqLeft_271_ = lean_ctor_get(v_toApplicative_265_, 3);
v_toSeqRight_272_ = lean_ctor_get(v_toApplicative_265_, 4);
v_isSharedCheck_294_ = !lean_is_exclusive(v_toApplicative_265_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_toApplicative_265_, 1);
lean_dec(v_unused_295_);
v___x_274_ = v_toApplicative_265_;
v_isShared_275_ = v_isSharedCheck_294_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_toSeqRight_272_);
lean_inc(v_toSeqLeft_271_);
lean_inc(v_toSeq_270_);
lean_inc(v_toFunctor_269_);
lean_dec(v_toApplicative_265_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_294_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v___x_285_; 
v___f_276_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__1));
v___f_277_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___closed__2));
lean_inc_ref(v_toFunctor_269_);
v___f_278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_278_, 0, v_toFunctor_269_);
v___f_279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_279_, 0, v_toFunctor_269_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___f_278_);
lean_ctor_set(v___x_280_, 1, v___f_279_);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_281_, 0, v_toSeqRight_272_);
v___f_282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_282_, 0, v_toSeqLeft_271_);
v___f_283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_283_, 0, v_toSeq_270_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v___f_281_);
lean_ctor_set(v___x_274_, 3, v___f_282_);
lean_ctor_set(v___x_274_, 2, v___f_283_);
lean_ctor_set(v___x_274_, 1, v___f_276_);
lean_ctor_set(v___x_274_, 0, v___x_280_);
v___x_285_ = v___x_274_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___f_276_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v___f_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v___f_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v___f_281_);
v___x_285_ = v_reuseFailAlloc_293_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___f_277_);
lean_ctor_set(v___x_267_, 0, v___x_285_);
v___x_287_ = v___x_267_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___f_277_);
v___x_287_ = v_reuseFailAlloc_292_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_25999__overap_290_; lean_object* v___x_291_; 
v___x_288_ = lean_box(0);
v___x_289_ = l_instInhabitedOfMonad___redArg(v___x_287_, v___x_288_);
v___x_25999__overap_290_ = lean_panic_fn_borrowed(v___x_289_, v_msg_259_);
lean_dec(v___x_289_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
v___x_291_ = lean_apply_3(v___x_25999__overap_290_, v___y_260_, v___y_261_, lean_box(0));
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg___boxed(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_302_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__2));
v___x_307_ = lean_unsigned_to_nat(21u);
v___x_308_ = lean_unsigned_to_nat(65u);
v___x_309_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__1));
v___x_310_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__0));
v___x_311_ = l_mkPanicMessageWithDecl(v___x_310_, v___x_309_, v___x_308_, v___x_307_, v___x_306_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(lean_object* v_preNode_312_, lean_object* v_postNode_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
switch(lean_obj_tag(v_x_315_))
{
case 0:
{
lean_object* v_i_319_; lean_object* v_t_320_; lean_object* v___x_321_; 
v_i_319_ = lean_ctor_get(v_x_315_, 0);
lean_inc_ref(v_i_319_);
v_t_320_ = lean_ctor_get(v_x_315_, 1);
lean_inc_ref(v_t_320_);
lean_dec_ref_known(v_x_315_, 2);
v___x_321_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_319_, v_x_314_);
v_x_314_ = v___x_321_;
v_x_315_ = v_t_320_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref_known(v_x_315_, 2);
lean_dec_ref(v_postNode_313_);
lean_dec_ref(v_preNode_312_);
v___x_323_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___closed__3);
v___x_324_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v___x_323_, v___y_316_, v___y_317_);
return v___x_324_;
}
else
{
lean_object* v_i_325_; lean_object* v_children_326_; lean_object* v_val_327_; lean_object* v___x_328_; 
v_i_325_ = lean_ctor_get(v_x_315_, 0);
lean_inc_ref_n(v_i_325_, 2);
v_children_326_ = lean_ctor_get(v_x_315_, 1);
lean_inc_ref_n(v_children_326_, 2);
lean_dec_ref_known(v_x_315_, 2);
v_val_327_ = lean_ctor_get(v_x_314_, 0);
lean_inc_n(v_val_327_, 2);
lean_inc_ref(v_preNode_312_);
lean_inc(v___y_317_);
lean_inc_ref(v___y_316_);
v___x_328_ = lean_apply_6(v_preNode_312_, v_val_327_, v_i_325_, v_children_326_, v___y_316_, v___y_317_, lean_box(0));
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; uint8_t v___x_330_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = lean_unbox(v_a_329_);
lean_dec(v_a_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_preNode_312_);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v_x_314_, 0);
lean_dec(v_unused_356_);
v___x_332_ = v_x_314_;
v_isShared_333_ = v_isSharedCheck_355_;
goto v_resetjp_331_;
}
else
{
lean_dec(v_x_314_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_355_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_box(0);
lean_inc(v___y_317_);
lean_inc_ref(v___y_316_);
v___x_335_ = lean_apply_7(v_postNode_313_, v_val_327_, v_i_325_, v_children_326_, v___x_334_, v___y_316_, v___y_317_, lean_box(0));
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_346_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_346_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v_a_336_);
v___x_341_ = v___x_332_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_341_);
v___x_343_ = v___x_338_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_del_object(v___x_332_);
v_a_347_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_335_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_335_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = l_Lean_Elab_Info_updateContext_x3f(v_x_314_, v_i_325_);
v___x_358_ = l_Lean_PersistentArray_toList___redArg(v_children_326_);
v___x_359_ = lean_box(0);
lean_inc_ref(v_postNode_313_);
v___x_360_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_312_, v_postNode_313_, v___x_357_, v___x_358_, v___x_359_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
lean_inc(v___y_317_);
lean_inc_ref(v___y_316_);
v___x_362_ = lean_apply_7(v_postNode_313_, v_val_327_, v_i_325_, v_children_326_, v_a_361_, v___y_316_, v___y_317_, lean_box(0));
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_371_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_371_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v_a_363_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_362_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_362_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v_val_327_);
lean_dec_ref(v_children_326_);
lean_dec_ref(v_i_325_);
lean_dec_ref(v_postNode_313_);
v_a_380_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_360_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_360_);
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
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_val_327_);
lean_dec_ref(v_children_326_);
lean_dec_ref(v_i_325_);
lean_dec_ref_known(v_x_314_, 1);
lean_dec_ref(v_postNode_313_);
lean_dec_ref(v_preNode_312_);
v_a_388_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_328_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_328_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
default: 
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_x_314_);
lean_dec_ref(v_postNode_313_);
lean_dec_ref(v_preNode_312_);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_x_315_, 0);
lean_dec(v_unused_404_);
v___x_397_ = v_x_315_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_x_315_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 0);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(lean_object* v_preNode_405_, lean_object* v_postNode_406_, lean_object* v___x_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v___x_407_);
lean_dec_ref(v_postNode_406_);
lean_dec_ref(v_preNode_405_);
v___x_413_ = l_List_reverse___redArg(v_x_409_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v_head_415_; lean_object* v_tail_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_434_; 
v_head_415_ = lean_ctor_get(v_x_408_, 0);
v_tail_416_ = lean_ctor_get(v_x_408_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_434_ == 0)
{
v___x_418_ = v_x_408_;
v_isShared_419_ = v_isSharedCheck_434_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_tail_416_);
lean_inc(v_head_415_);
lean_dec(v_x_408_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_434_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; 
lean_inc(v___x_407_);
lean_inc_ref(v_postNode_406_);
lean_inc_ref(v_preNode_405_);
v___x_420_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_405_, v_postNode_406_, v___x_407_, v_head_415_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_x_409_);
lean_ctor_set(v___x_418_, 0, v_a_421_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_421_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_x_409_);
v___x_423_ = v_reuseFailAlloc_425_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v_x_408_ = v_tail_416_;
v_x_409_ = v___x_423_;
goto _start;
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_del_object(v___x_418_);
lean_dec(v_tail_416_);
lean_dec(v_x_409_);
lean_dec(v___x_407_);
lean_dec_ref(v_postNode_406_);
lean_dec_ref(v_preNode_405_);
v_a_426_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_420_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_420_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg___boxed(lean_object* v_preNode_435_, lean_object* v_postNode_436_, lean_object* v___x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_435_, v_postNode_436_, v___x_437_, v_x_438_, v_x_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg___boxed(lean_object* v_preNode_444_, lean_object* v_postNode_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_444_, v_postNode_445_, v_x_446_, v_x_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(lean_object* v_preNode_452_, lean_object* v_postNode_453_, lean_object* v_ctx_x3f_454_, lean_object* v_t_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___lam__0___boxed), 8, 1);
lean_closure_set(v___f_459_, 0, v_postNode_453_);
v___x_460_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_452_, v___f_459_, v_ctx_x3f_454_, v_t_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_468_; 
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_460_, 0);
lean_dec(v_unused_469_);
v___x_462_ = v___x_460_;
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
else
{
lean_dec(v___x_460_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_box(0);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_460_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_460_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11___boxed(lean_object* v_preNode_478_, lean_object* v_postNode_479_, lean_object* v_ctx_x3f_480_, lean_object* v_t_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v_preNode_478_, v_postNode_479_, v_ctx_x3f_480_, v_t_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_485_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(uint8_t v___y_487_, uint8_t v_suppressElabErrors_488_, lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_489_) == 1)
{
lean_object* v_pre_490_; 
v_pre_490_ = lean_ctor_get(v_x_489_, 0);
if (lean_obj_tag(v_pre_490_) == 0)
{
lean_object* v_str_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_str_491_ = lean_ctor_get(v_x_489_, 1);
v___x_492_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___closed__0));
v___x_493_ = lean_string_dec_eq(v_str_491_, v___x_492_);
if (v___x_493_ == 0)
{
return v___y_487_;
}
else
{
return v_suppressElabErrors_488_;
}
}
else
{
return v___y_487_;
}
}
else
{
return v___y_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed(lean_object* v___y_494_, lean_object* v_suppressElabErrors_495_, lean_object* v_x_496_){
_start:
{
uint8_t v___y_29431__boxed_497_; uint8_t v_suppressElabErrors_boxed_498_; uint8_t v_res_499_; lean_object* v_r_500_; 
v___y_29431__boxed_497_ = lean_unbox(v___y_494_);
v_suppressElabErrors_boxed_498_ = lean_unbox(v_suppressElabErrors_495_);
v_res_499_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(v___y_29431__boxed_497_, v_suppressElabErrors_boxed_498_, v_x_496_);
lean_dec(v_x_496_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_501_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__0);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
lean_ctor_set(v___x_506_, 3, v___x_505_);
lean_ctor_set(v___x_506_, 4, v___x_504_);
lean_ctor_set(v___x_506_, 5, v___x_504_);
lean_ctor_set(v___x_506_, 6, v___x_504_);
lean_ctor_set(v___x_506_, 7, v___x_504_);
lean_ctor_set(v___x_506_, 8, v___x_504_);
lean_ctor_set(v___x_506_, 9, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(32u);
v___x_508_ = lean_mk_empty_array_with_capacity(v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4(void){
_start:
{
size_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_510_ = ((size_t)5ULL);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_unsigned_to_nat(32u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
v___x_514_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__3);
v___x_515_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_511_);
lean_ctor_set(v___x_515_, 3, v___x_511_);
lean_ctor_set_usize(v___x_515_, 4, v___x_510_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = lean_box(1);
v___x_517_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_518_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__1);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(lean_object* v_msgData_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v___x_525_; lean_object* v_scopes_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_opts_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_523_ = lean_st_ref_get(v___y_521_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v___x_525_ = lean_st_ref_get(v___y_521_);
v_scopes_526_ = lean_ctor_get(v___x_525_, 2);
lean_inc(v_scopes_526_);
lean_dec(v___x_525_);
v___x_527_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_528_ = l_List_head_x21___redArg(v___x_527_, v_scopes_526_);
lean_dec(v_scopes_526_);
v_opts_529_ = lean_ctor_get(v___x_528_, 1);
lean_inc_ref(v_opts_529_);
lean_dec(v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__2);
v___x_531_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__5);
v___x_532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_532_, 0, v_env_524_);
lean_ctor_set(v___x_532_, 1, v___x_530_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
lean_ctor_set(v___x_532_, 3, v_opts_529_);
v___x_533_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_msgData_520_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___boxed(lean_object* v_msgData_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_535_, v___y_536_);
lean_dec(v___y_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(lean_object* v_ref_540_, lean_object* v_msgData_541_, uint8_t v_severity_542_, uint8_t v_isSilent_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___y_548_; uint8_t v___y_549_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; uint8_t v___y_612_; uint8_t v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; lean_object* v___y_616_; uint8_t v___y_640_; uint8_t v___y_641_; lean_object* v___y_642_; uint8_t v___y_643_; lean_object* v___y_644_; uint8_t v___y_648_; uint8_t v___y_649_; uint8_t v___y_650_; uint8_t v___x_665_; uint8_t v___y_667_; uint8_t v___y_668_; uint8_t v___y_669_; uint8_t v___y_671_; uint8_t v___x_683_; 
v___x_665_ = 2;
v___x_683_ = l_Lean_instBEqMessageSeverity_beq(v_severity_542_, v___x_665_);
if (v___x_683_ == 0)
{
v___y_671_ = v___x_683_;
goto v___jp_670_;
}
else
{
uint8_t v___x_684_; 
lean_inc_ref(v_msgData_541_);
v___x_684_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_541_);
v___y_671_ = v___x_684_;
goto v___jp_670_;
}
v___jp_547_:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_Command_getScope___redArg(v___y_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = l_Lean_Elab_Command_getScope___redArg(v___y_555_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_594_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_594_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_594_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_594_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v_currNamespace_564_; lean_object* v_openDecls_565_; lean_object* v_env_566_; lean_object* v_messages_567_; lean_object* v_scopes_568_; lean_object* v_usedQuotCtxts_569_; lean_object* v_nextMacroScope_570_; lean_object* v_maxRecDepth_571_; lean_object* v_ngen_572_; lean_object* v_auxDeclNGen_573_; lean_object* v_infoState_574_; lean_object* v_traceState_575_; lean_object* v_snapshotTasks_576_; lean_object* v_prevLinterStates_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_593_; 
v___x_563_ = lean_st_ref_take(v___y_555_);
v_currNamespace_564_ = lean_ctor_get(v_a_557_, 2);
lean_inc(v_currNamespace_564_);
lean_dec(v_a_557_);
v_openDecls_565_ = lean_ctor_get(v_a_559_, 3);
lean_inc(v_openDecls_565_);
lean_dec(v_a_559_);
v_env_566_ = lean_ctor_get(v___x_563_, 0);
v_messages_567_ = lean_ctor_get(v___x_563_, 1);
v_scopes_568_ = lean_ctor_get(v___x_563_, 2);
v_usedQuotCtxts_569_ = lean_ctor_get(v___x_563_, 3);
v_nextMacroScope_570_ = lean_ctor_get(v___x_563_, 4);
v_maxRecDepth_571_ = lean_ctor_get(v___x_563_, 5);
v_ngen_572_ = lean_ctor_get(v___x_563_, 6);
v_auxDeclNGen_573_ = lean_ctor_get(v___x_563_, 7);
v_infoState_574_ = lean_ctor_get(v___x_563_, 8);
v_traceState_575_ = lean_ctor_get(v___x_563_, 9);
v_snapshotTasks_576_ = lean_ctor_get(v___x_563_, 10);
v_prevLinterStates_577_ = lean_ctor_get(v___x_563_, 11);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_593_ == 0)
{
v___x_579_ = v___x_563_;
v_isShared_580_ = v_isSharedCheck_593_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_prevLinterStates_577_);
lean_inc(v_snapshotTasks_576_);
lean_inc(v_traceState_575_);
lean_inc(v_infoState_574_);
lean_inc(v_auxDeclNGen_573_);
lean_inc(v_ngen_572_);
lean_inc(v_maxRecDepth_571_);
lean_inc(v_nextMacroScope_570_);
lean_inc(v_usedQuotCtxts_569_);
lean_inc(v_scopes_568_);
lean_inc(v_messages_567_);
lean_inc(v_env_566_);
lean_dec(v___x_563_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_593_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_currNamespace_564_);
lean_ctor_set(v___x_581_, 1, v_openDecls_565_);
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___y_551_);
lean_inc_ref(v___y_548_);
lean_inc_ref(v___y_554_);
v___x_583_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_583_, 0, v___y_554_);
lean_ctor_set(v___x_583_, 1, v___y_552_);
lean_ctor_set(v___x_583_, 2, v___y_553_);
lean_ctor_set(v___x_583_, 3, v___y_548_);
lean_ctor_set(v___x_583_, 4, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5, v___y_550_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5 + 1, v___y_549_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5 + 2, v_isSilent_543_);
v___x_584_ = l_Lean_MessageLog_add(v___x_583_, v_messages_567_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v___x_584_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_env_566_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_scopes_568_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_usedQuotCtxts_569_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v_nextMacroScope_570_);
lean_ctor_set(v_reuseFailAlloc_592_, 5, v_maxRecDepth_571_);
lean_ctor_set(v_reuseFailAlloc_592_, 6, v_ngen_572_);
lean_ctor_set(v_reuseFailAlloc_592_, 7, v_auxDeclNGen_573_);
lean_ctor_set(v_reuseFailAlloc_592_, 8, v_infoState_574_);
lean_ctor_set(v_reuseFailAlloc_592_, 9, v_traceState_575_);
lean_ctor_set(v_reuseFailAlloc_592_, 10, v_snapshotTasks_576_);
lean_ctor_set(v_reuseFailAlloc_592_, 11, v_prevLinterStates_577_);
v___x_586_ = v_reuseFailAlloc_592_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = lean_st_ref_set(v___y_555_, v___x_586_);
v___x_588_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_588_);
v___x_590_ = v___x_561_;
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
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_a_557_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_551_);
v_a_595_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_558_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_558_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_551_);
v_a_603_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_556_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_556_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
v___jp_611_:
{
lean_object* v_fileName_617_; lean_object* v_fileMap_618_; uint8_t v_suppressElabErrors_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_638_; 
v_fileName_617_ = lean_ctor_get(v___y_544_, 0);
v_fileMap_618_ = lean_ctor_get(v___y_544_, 1);
v_suppressElabErrors_619_ = lean_ctor_get_uint8(v___y_544_, sizeof(void*)*10);
v___x_620_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_541_);
v___x_621_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v___x_620_, v___y_545_);
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_638_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_638_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_638_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc_ref_n(v_fileMap_618_, 2);
v___x_626_ = l_Lean_FileMap_toPosition(v_fileMap_618_, v___y_614_);
lean_dec(v___y_614_);
v___x_627_ = l_Lean_FileMap_toPosition(v_fileMap_618_, v___y_616_);
lean_dec(v___y_616_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___closed__0));
if (v_suppressElabErrors_619_ == 0)
{
lean_del_object(v___x_624_);
v___y_548_ = v___x_629_;
v___y_549_ = v___y_613_;
v___y_550_ = v___y_615_;
v___y_551_ = v_a_622_;
v___y_552_ = v___x_626_;
v___y_553_ = v___x_628_;
v___y_554_ = v_fileName_617_;
v___y_555_ = v___y_545_;
goto v___jp_547_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___f_632_; uint8_t v___x_633_; 
v___x_630_ = lean_box(v___y_612_);
v___x_631_ = lean_box(v_suppressElabErrors_619_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0___boxed), 3, 2);
lean_closure_set(v___f_632_, 0, v___x_630_);
lean_closure_set(v___f_632_, 1, v___x_631_);
lean_inc(v_a_622_);
v___x_633_ = l_Lean_MessageData_hasTag(v___f_632_, v_a_622_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec_ref_known(v___x_628_, 1);
lean_dec_ref(v___x_626_);
lean_dec(v_a_622_);
v___x_634_ = lean_box(0);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_634_);
v___x_636_ = v___x_624_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_del_object(v___x_624_);
v___y_548_ = v___x_629_;
v___y_549_ = v___y_613_;
v___y_550_ = v___y_615_;
v___y_551_ = v_a_622_;
v___y_552_ = v___x_626_;
v___y_553_ = v___x_628_;
v___y_554_ = v_fileName_617_;
v___y_555_ = v___y_545_;
goto v___jp_547_;
}
}
}
}
v___jp_639_:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Syntax_getTailPos_x3f(v___y_642_, v___y_643_);
lean_dec(v___y_642_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_inc(v___y_644_);
v___y_612_ = v___y_640_;
v___y_613_ = v___y_641_;
v___y_614_ = v___y_644_;
v___y_615_ = v___y_643_;
v___y_616_ = v___y_644_;
goto v___jp_611_;
}
else
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
v___y_612_ = v___y_640_;
v___y_613_ = v___y_641_;
v___y_614_ = v___y_644_;
v___y_615_ = v___y_643_;
v___y_616_ = v_val_646_;
goto v___jp_611_;
}
}
v___jp_647_:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Elab_Command_getRef___redArg(v___y_544_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v_ref_653_; lean_object* v___x_654_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v_ref_653_ = l_Lean_replaceRef(v_ref_540_, v_a_652_);
lean_dec(v_a_652_);
v___x_654_ = l_Lean_Syntax_getPos_x3f(v_ref_653_, v___y_649_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___y_640_ = v___y_648_;
v___y_641_ = v___y_650_;
v___y_642_ = v_ref_653_;
v___y_643_ = v___y_649_;
v___y_644_ = v___x_655_;
goto v___jp_639_;
}
else
{
lean_object* v_val_656_; 
v_val_656_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v___x_654_, 1);
v___y_640_ = v___y_648_;
v___y_641_ = v___y_650_;
v___y_642_ = v_ref_653_;
v___y_643_ = v___y_649_;
v___y_644_ = v_val_656_;
goto v___jp_639_;
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_msgData_541_);
v_a_657_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_651_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_651_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
v___jp_666_:
{
if (v___y_669_ == 0)
{
v___y_648_ = v___y_667_;
v___y_649_ = v___y_668_;
v___y_650_ = v_severity_542_;
goto v___jp_647_;
}
else
{
v___y_648_ = v___y_667_;
v___y_649_ = v___y_668_;
v___y_650_ = v___x_665_;
goto v___jp_647_;
}
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
lean_object* v___x_672_; lean_object* v_scopes_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_opts_676_; uint8_t v___x_677_; uint8_t v___x_678_; 
v___x_672_ = lean_st_ref_get(v___y_545_);
v_scopes_673_ = lean_ctor_get(v___x_672_, 2);
lean_inc(v_scopes_673_);
lean_dec(v___x_672_);
v___x_674_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_675_ = l_List_head_x21___redArg(v___x_674_, v_scopes_673_);
lean_dec(v_scopes_673_);
v_opts_676_ = lean_ctor_get(v___x_675_, 1);
lean_inc_ref(v_opts_676_);
lean_dec(v___x_675_);
v___x_677_ = 1;
v___x_678_ = l_Lean_instBEqMessageSeverity_beq(v_severity_542_, v___x_677_);
if (v___x_678_ == 0)
{
lean_dec_ref(v_opts_676_);
v___y_667_ = v___y_671_;
v___y_668_ = v___y_671_;
v___y_669_ = v___x_678_;
goto v___jp_666_;
}
else
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = l_Lean_warningAsError;
v___x_680_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v_opts_676_, v___x_679_);
lean_dec_ref(v_opts_676_);
v___y_667_ = v___y_671_;
v___y_668_ = v___y_671_;
v___y_669_ = v___x_680_;
goto v___jp_666_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_msgData_541_);
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___boxed(lean_object* v_ref_685_, lean_object* v_msgData_686_, lean_object* v_severity_687_, lean_object* v_isSilent_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v_severity_boxed_692_; uint8_t v_isSilent_boxed_693_; lean_object* v_res_694_; 
v_severity_boxed_692_ = lean_unbox(v_severity_687_);
v_isSilent_boxed_693_ = lean_unbox(v_isSilent_688_);
v_res_694_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_685_, v_msgData_686_, v_severity_boxed_692_, v_isSilent_boxed_693_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_ref_685_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(lean_object* v_ref_695_, lean_object* v_msgData_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; 
v___x_700_ = 1;
v___x_701_ = 0;
v___x_702_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20(v_ref_695_, v_msgData_696_, v___x_700_, v___x_701_, v___y_697_, v___y_698_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15___boxed(lean_object* v_ref_703_, lean_object* v_msgData_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_ref_703_, v_msgData_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v_ref_703_);
return v_res_708_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__0));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__2));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(lean_object* v_linterOption_715_, lean_object* v_stx_716_, lean_object* v_msg_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_name_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_739_; 
v_name_721_ = lean_ctor_get(v_linterOption_715_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_linterOption_715_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v_linterOption_715_, 1);
lean_dec(v_unused_740_);
v___x_723_ = v_linterOption_715_;
v_isShared_724_ = v_isSharedCheck_739_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_name_721_);
lean_dec(v_linterOption_715_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_739_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__1);
lean_inc(v_name_721_);
v___x_726_ = l_Lean_MessageData_ofName(v_name_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 7);
lean_ctor_set(v___x_723_, 1, v___x_726_);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_738_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_disable_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_729_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v_disable_731_ = l_Lean_MessageData_note(v___x_730_);
v___x_732_ = l_Lean_Linter_linterMessageTag;
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v_msg_717_);
lean_ctor_set(v___x_733_, 1, v_disable_731_);
v___x_734_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_735_, 0, v_name_721_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc(v_stx_716_);
v___x_736_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_736_, 0, v_stx_716_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_stx_716_, v___x_736_, v___y_718_, v___y_719_);
lean_dec(v_stx_716_);
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object* v_linterOption_741_, lean_object* v_stx_742_, lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_linterOption_741_, v_stx_742_, v_msg_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_748_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_751_ = lean_box(1);
v___x_752_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1);
v___x_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
lean_ctor_set(v___x_754_, 2, v___x_751_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(lean_object* v_val_757_, uint8_t v_a_758_, lean_object* v___x_759_, lean_object* v___f_760_, lean_object* v_ci_761_, lean_object* v_info_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_st_ref_get(v_val_757_);
v___x_768_ = lean_unbox(v___x_767_);
lean_dec(v___x_767_);
if (v___x_768_ == 0)
{
if (lean_obj_tag(v_info_762_) == 0)
{
lean_object* v_toCommandContextInfo_769_; lean_object* v_i_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_845_; 
v_toCommandContextInfo_769_ = lean_ctor_get(v_ci_761_, 0);
lean_inc_ref(v_toCommandContextInfo_769_);
v_i_770_ = lean_ctor_get(v_info_762_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_info_762_);
if (v_isSharedCheck_845_ == 0)
{
v___x_772_ = v_info_762_;
v_isShared_773_ = v_isSharedCheck_845_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_i_770_);
lean_dec(v_info_762_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_845_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_parentDecl_x3f_774_; lean_object* v_autoImplicits_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_843_; 
v_parentDecl_x3f_774_ = lean_ctor_get(v_ci_761_, 1);
v_autoImplicits_775_ = lean_ctor_get(v_ci_761_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_ci_761_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_ci_761_, 0);
lean_dec(v_unused_844_);
v___x_777_ = v_ci_761_;
v_isShared_778_ = v_isSharedCheck_843_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_autoImplicits_775_);
lean_inc(v_parentDecl_x3f_774_);
lean_dec(v_ci_761_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_843_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_env_779_; lean_object* v_cmdEnv_x3f_780_; lean_object* v_fileMap_781_; lean_object* v_options_782_; lean_object* v_currNamespace_783_; lean_object* v_openDecls_784_; lean_object* v_ngen_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_841_; 
v_env_779_ = lean_ctor_get(v_toCommandContextInfo_769_, 0);
v_cmdEnv_x3f_780_ = lean_ctor_get(v_toCommandContextInfo_769_, 1);
v_fileMap_781_ = lean_ctor_get(v_toCommandContextInfo_769_, 2);
v_options_782_ = lean_ctor_get(v_toCommandContextInfo_769_, 4);
v_currNamespace_783_ = lean_ctor_get(v_toCommandContextInfo_769_, 5);
v_openDecls_784_ = lean_ctor_get(v_toCommandContextInfo_769_, 6);
v_ngen_785_ = lean_ctor_get(v_toCommandContextInfo_769_, 7);
v_isSharedCheck_841_ = !lean_is_exclusive(v_toCommandContextInfo_769_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v_toCommandContextInfo_769_, 3);
lean_dec(v_unused_842_);
v___x_787_ = v_toCommandContextInfo_769_;
v_isShared_788_ = v_isSharedCheck_841_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_ngen_785_);
lean_inc(v_openDecls_784_);
lean_inc(v_currNamespace_783_);
lean_inc(v_options_782_);
lean_inc(v_fileMap_781_);
lean_inc(v_cmdEnv_x3f_780_);
lean_inc(v_env_779_);
lean_dec(v_toCommandContextInfo_769_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_841_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_toElabInfo_789_; lean_object* v_mctxBefore_790_; lean_object* v_goalsBefore_791_; lean_object* v_mctxAfter_792_; lean_object* v_goalsAfter_793_; lean_object* v___y_795_; lean_object* v___x_826_; 
v_toElabInfo_789_ = lean_ctor_get(v_i_770_, 0);
lean_inc_ref(v_toElabInfo_789_);
v_mctxBefore_790_ = lean_ctor_get(v_i_770_, 1);
lean_inc_ref(v_mctxBefore_790_);
v_goalsBefore_791_ = lean_ctor_get(v_i_770_, 2);
lean_inc(v_goalsBefore_791_);
v_mctxAfter_792_ = lean_ctor_get(v_i_770_, 3);
lean_inc_ref(v_mctxAfter_792_);
v_goalsAfter_793_ = lean_ctor_get(v_i_770_, 4);
lean_inc(v_goalsAfter_793_);
lean_dec_ref(v_i_770_);
lean_inc_ref(v_ngen_785_);
lean_inc(v_openDecls_784_);
lean_inc(v_currNamespace_783_);
lean_inc_ref(v_options_782_);
lean_inc_ref(v_fileMap_781_);
lean_inc(v_cmdEnv_x3f_780_);
lean_inc_ref(v_env_779_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 3, v_mctxBefore_790_);
v___x_826_ = v___x_787_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_env_779_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_cmdEnv_x3f_780_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_fileMap_781_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_mctxBefore_790_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_options_782_);
lean_ctor_set(v_reuseFailAlloc_840_, 5, v_currNamespace_783_);
lean_ctor_set(v_reuseFailAlloc_840_, 6, v_openDecls_784_);
lean_ctor_set(v_reuseFailAlloc_840_, 7, v_ngen_785_);
v___x_826_ = v_reuseFailAlloc_840_;
goto v_reusejp_825_;
}
v___jp_794_:
{
if (lean_obj_tag(v___y_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_772_);
v_a_796_ = lean_ctor_get(v___y_795_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___y_795_);
if (v_isSharedCheck_809_ == 0)
{
v___x_798_ = v___y_795_;
v_isShared_799_ = v_isSharedCheck_809_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___y_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_809_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 1)
{
lean_object* v_val_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_stx_803_; lean_object* v___x_804_; 
lean_del_object(v___x_798_);
v_val_800_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_a_796_, 1);
v___x_801_ = lean_box(v_a_758_);
v___x_802_ = lean_st_ref_set(v_val_757_, v___x_801_);
v_stx_803_ = lean_ctor_get(v_toElabInfo_789_, 1);
lean_inc(v_stx_803_);
lean_dec_ref(v_toElabInfo_789_);
v___x_804_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___x_759_, v_stx_803_, v_val_800_, v___y_764_, v___y_765_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_a_796_);
lean_dec_ref(v_toElabInfo_789_);
lean_dec_ref(v___x_759_);
v___x_805_ = lean_box(0);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_805_);
v___x_807_ = v___x_798_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_toElabInfo_789_);
lean_dec_ref(v___x_759_);
v_a_810_ = lean_ctor_get(v___y_795_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___y_795_);
if (v_isSharedCheck_824_ == 0)
{
v___x_812_ = v___y_795_;
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___y_795_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_824_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_ref_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v_ref_814_ = lean_ctor_get(v___y_764_, 7);
v___x_815_ = lean_io_error_to_string(v_a_810_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 3);
lean_ctor_set(v___x_772_, 0, v___x_815_);
v___x_817_ = v___x_772_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_823_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = l_Lean_MessageData_ofFormat(v___x_817_);
lean_inc(v_ref_814_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_ref_814_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
lean_inc_ref(v_autoImplicits_775_);
lean_inc(v_parentDecl_x3f_774_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_826_);
v___x_828_ = v___x_777_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_parentDecl_x3f_774_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_autoImplicits_775_);
v___x_828_ = v_reuseFailAlloc_839_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3));
lean_inc_ref(v___f_760_);
v___x_831_ = lean_apply_2(v___f_760_, v___x_830_, v_goalsBefore_791_);
v___x_832_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_828_, v___x_829_, v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
if (lean_obj_tag(v_a_833_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_834_, 0, v_env_779_);
lean_ctor_set(v___x_834_, 1, v_cmdEnv_x3f_780_);
lean_ctor_set(v___x_834_, 2, v_fileMap_781_);
lean_ctor_set(v___x_834_, 3, v_mctxAfter_792_);
lean_ctor_set(v___x_834_, 4, v_options_782_);
lean_ctor_set(v___x_834_, 5, v_currNamespace_783_);
lean_ctor_set(v___x_834_, 6, v_openDecls_784_);
lean_ctor_set(v___x_834_, 7, v_ngen_785_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_parentDecl_x3f_774_);
lean_ctor_set(v___x_835_, 2, v_autoImplicits_775_);
v___x_836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4));
v___x_837_ = lean_apply_2(v___f_760_, v___x_836_, v_goalsAfter_793_);
v___x_838_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_835_, v___x_829_, v___x_837_);
v___y_795_ = v___x_838_;
goto v___jp_794_;
}
else
{
lean_dec_ref_known(v_a_833_, 1);
lean_dec(v_goalsAfter_793_);
lean_dec_ref(v_mctxAfter_792_);
lean_dec_ref(v_ngen_785_);
lean_dec(v_openDecls_784_);
lean_dec(v_currNamespace_783_);
lean_dec_ref(v_options_782_);
lean_dec_ref(v_fileMap_781_);
lean_dec(v_cmdEnv_x3f_780_);
lean_dec_ref(v_env_779_);
lean_dec_ref(v_autoImplicits_775_);
lean_dec(v_parentDecl_x3f_774_);
lean_dec_ref(v___f_760_);
v___y_795_ = v___x_832_;
goto v___jp_794_;
}
}
else
{
lean_dec(v_goalsAfter_793_);
lean_dec_ref(v_mctxAfter_792_);
lean_dec_ref(v_ngen_785_);
lean_dec(v_openDecls_784_);
lean_dec(v_currNamespace_783_);
lean_dec_ref(v_options_782_);
lean_dec_ref(v_fileMap_781_);
lean_dec(v_cmdEnv_x3f_780_);
lean_dec_ref(v_env_779_);
lean_dec_ref(v_autoImplicits_775_);
lean_dec(v_parentDecl_x3f_774_);
lean_dec_ref(v___f_760_);
v___y_795_ = v___x_832_;
goto v___jp_794_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v_info_762_);
lean_dec_ref(v_ci_761_);
lean_dec_ref(v___f_760_);
lean_dec_ref(v___x_759_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_info_762_);
lean_dec_ref(v_ci_761_);
lean_dec_ref(v___f_760_);
lean_dec_ref(v___x_759_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed(lean_object* v_val_850_, lean_object* v_a_851_, lean_object* v___x_852_, lean_object* v___f_853_, lean_object* v_ci_854_, lean_object* v_info_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_a_29905__boxed_860_; lean_object* v_res_861_; 
v_a_29905__boxed_860_ = lean_unbox(v_a_851_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(v_val_850_, v_a_29905__boxed_860_, v___x_852_, v___f_853_, v_ci_854_, v_info_855_, v_x_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_x_856_);
lean_dec(v_val_850_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(lean_object* v___x_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v___x_865_; 
lean_dec_ref(v___x_862_);
v___x_865_ = lean_array_to_list(v_a_864_);
return v___x_865_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_head_866_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_head_866_);
v_tail_867_ = lean_ctor_get(v_a_863_, 1);
lean_inc(v_tail_867_);
lean_dec_ref_known(v_a_863_, 2);
v_fst_868_ = lean_ctor_get(v_head_866_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v_head_866_, 1);
lean_inc(v_snd_869_);
lean_dec(v_head_866_);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_nat_dec_lt(v___x_870_, v_snd_869_);
lean_dec(v_snd_869_);
if (v___x_871_ == 0)
{
lean_dec(v_fst_868_);
v_a_863_ = v_tail_867_;
goto _start;
}
else
{
uint8_t v___x_873_; 
lean_inc(v_fst_868_);
lean_inc_ref(v___x_862_);
v___x_873_ = l_Lean_getReducibilityStatusCore(v___x_862_, v_fst_868_);
if (v___x_873_ == 1)
{
uint8_t v___x_874_; 
lean_inc_ref(v___x_862_);
v___x_874_ = l_Lean_Meta_isInstanceCore(v___x_862_, v_fst_868_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = l_Lean_MessageData_ofConstName(v_fst_868_, v___x_874_);
v___x_876_ = lean_array_push(v_a_864_, v___x_875_);
v_a_863_ = v_tail_867_;
v_a_864_ = v___x_876_;
goto _start;
}
else
{
lean_dec(v_fst_868_);
v_a_863_ = v_tail_867_;
goto _start;
}
}
else
{
lean_dec(v_fst_868_);
v_a_863_ = v_tail_867_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(lean_object* v_o_882_, lean_object* v_k_883_, uint8_t v_v_884_){
_start:
{
lean_object* v_map_885_; uint8_t v_hasTrace_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_900_; 
v_map_885_ = lean_ctor_get(v_o_882_, 0);
v_hasTrace_886_ = lean_ctor_get_uint8(v_o_882_, sizeof(void*)*1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_o_882_);
if (v_isSharedCheck_900_ == 0)
{
v___x_888_ = v_o_882_;
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_map_885_);
lean_dec(v_o_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_890_, 0, v_v_884_);
lean_inc(v_k_883_);
v___x_891_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_883_, v___x_890_, v_map_885_);
if (v_hasTrace_886_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_895_; 
v___x_892_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0));
v___x_893_ = l_Lean_Name_isPrefixOf(v___x_892_, v_k_883_);
lean_dec(v_k_883_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_895_ = v___x_888_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_891_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_893_);
return v___x_895_;
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v_k_883_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_899_, sizeof(void*)*1, v_hasTrace_886_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___boxed(lean_object* v_o_901_, lean_object* v_k_902_, lean_object* v_v_903_){
_start:
{
uint8_t v_v_boxed_904_; lean_object* v_res_905_; 
v_v_boxed_904_ = lean_unbox(v_v_903_);
v_res_905_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_o_901_, v_k_902_, v_v_boxed_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(lean_object* v_opts_906_, lean_object* v_opt_907_, uint8_t v_val_908_){
_start:
{
lean_object* v_name_909_; lean_object* v___x_910_; 
v_name_909_ = lean_ctor_get(v_opt_907_, 0);
lean_inc(v_name_909_);
lean_dec_ref(v_opt_907_);
v___x_910_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_opts_906_, v_name_909_, v_val_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(lean_object* v_opts_911_, lean_object* v_opt_912_, lean_object* v_val_913_){
_start:
{
uint8_t v_val_boxed_914_; lean_object* v_res_915_; 
v_val_boxed_914_ = lean_unbox(v_val_913_);
v_res_915_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_opts_911_, v_opt_912_, v_val_boxed_914_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(lean_object* v_f_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_i_919_, lean_object* v_acc_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_array_get_size(v_keys_917_);
v___x_922_ = lean_nat_dec_lt(v_i_919_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec(v_i_919_);
lean_dec_ref(v_f_916_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_acc_920_);
return v___x_923_;
}
else
{
lean_object* v_k_924_; lean_object* v_v_925_; lean_object* v___x_926_; 
v_k_924_ = lean_array_fget_borrowed(v_keys_917_, v_i_919_);
v_v_925_ = lean_array_fget_borrowed(v_vals_918_, v_i_919_);
lean_inc_ref(v_f_916_);
lean_inc(v_v_925_);
lean_inc(v_k_924_);
v___x_926_ = lean_apply_3(v_f_916_, v_acc_920_, v_k_924_, v_v_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_dec(v_i_919_);
lean_dec_ref(v_f_916_);
return v___x_926_;
}
else
{
lean_object* v_a_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_add(v_i_919_, v___x_928_);
lean_dec(v_i_919_);
v_i_919_ = v___x_929_;
v_acc_920_ = v_a_927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg___boxed(lean_object* v_f_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_i_934_, lean_object* v_acc_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_931_, v_keys_932_, v_vals_933_, v_i_934_, v_acc_935_);
lean_dec_ref(v_vals_933_);
lean_dec_ref(v_keys_932_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(lean_object* v_f_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_es_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_960_; 
v_es_940_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_960_ == 0)
{
v___x_942_ = v_x_938_;
v_isShared_943_ = v_isSharedCheck_960_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_es_940_);
lean_dec(v_x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_960_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_array_get_size(v_es_940_);
v___x_946_ = lean_nat_dec_lt(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_948_; 
lean_dec_ref(v_es_940_);
lean_dec_ref(v_f_937_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 1);
lean_ctor_set(v___x_942_, 0, v_x_939_);
v___x_948_ = v___x_942_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_x_939_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
uint8_t v___x_950_; 
v___x_950_ = lean_nat_dec_le(v___x_945_, v___x_945_);
if (v___x_950_ == 0)
{
if (v___x_946_ == 0)
{
lean_object* v___x_952_; 
lean_dec_ref(v_es_940_);
lean_dec_ref(v_f_937_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 1);
lean_ctor_set(v___x_942_, 0, v_x_939_);
v___x_952_ = v___x_942_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_x_939_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
lean_del_object(v___x_942_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = lean_usize_of_nat(v___x_945_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_937_, v_es_940_, v___x_954_, v___x_955_, v_x_939_);
lean_dec_ref(v_es_940_);
return v___x_956_;
}
}
else
{
size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
lean_del_object(v___x_942_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = lean_usize_of_nat(v___x_945_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_937_, v_es_940_, v___x_957_, v___x_958_, v_x_939_);
lean_dec_ref(v_es_940_);
return v___x_959_;
}
}
}
}
else
{
lean_object* v_ks_961_; lean_object* v_vs_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_ks_961_ = lean_ctor_get(v_x_938_, 0);
lean_inc_ref(v_ks_961_);
v_vs_962_ = lean_ctor_get(v_x_938_, 1);
lean_inc_ref(v_vs_962_);
lean_dec_ref_known(v_x_938_, 2);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_937_, v_ks_961_, v_vs_962_, v___x_963_, v_x_939_);
lean_dec_ref(v_vs_962_);
lean_dec_ref(v_ks_961_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(lean_object* v_f_965_, lean_object* v_as_966_, size_t v_i_967_, size_t v_stop_968_, lean_object* v_b_969_){
_start:
{
lean_object* v_a_971_; lean_object* v___y_976_; uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_eq(v_i_967_, v_stop_968_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_array_uget_borrowed(v_as_966_, v_i_967_);
switch(lean_obj_tag(v___x_979_))
{
case 0:
{
lean_object* v_key_980_; lean_object* v_val_981_; lean_object* v___x_982_; 
v_key_980_ = lean_ctor_get(v___x_979_, 0);
v_val_981_ = lean_ctor_get(v___x_979_, 1);
lean_inc_ref(v_f_965_);
lean_inc(v_val_981_);
lean_inc(v_key_980_);
v___x_982_ = lean_apply_3(v_f_965_, v_b_969_, v_key_980_, v_val_981_);
v___y_976_ = v___x_982_;
goto v___jp_975_;
}
case 1:
{
lean_object* v_node_983_; lean_object* v___x_984_; 
v_node_983_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_node_983_);
lean_inc_ref(v_f_965_);
v___x_984_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_965_, v_node_983_, v_b_969_);
v___y_976_ = v___x_984_;
goto v___jp_975_;
}
default: 
{
v_a_971_ = v_b_969_;
goto v___jp_970_;
}
}
}
else
{
lean_object* v___x_985_; 
lean_dec_ref(v_f_965_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_b_969_);
return v___x_985_;
}
v___jp_970_:
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_967_, v___x_972_);
v_i_967_ = v___x_973_;
v_b_969_ = v_a_971_;
goto _start;
}
v___jp_975_:
{
if (lean_obj_tag(v___y_976_) == 0)
{
lean_dec_ref(v_f_965_);
return v___y_976_;
}
else
{
lean_object* v_a_977_; 
v_a_977_ = lean_ctor_get(v___y_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___y_976_, 1);
v_a_971_ = v_a_977_;
goto v___jp_970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg___boxed(lean_object* v_f_986_, lean_object* v_as_987_, lean_object* v_i_988_, lean_object* v_stop_989_, lean_object* v_b_990_){
_start:
{
size_t v_i_boxed_991_; size_t v_stop_boxed_992_; lean_object* v_res_993_; 
v_i_boxed_991_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_stop_boxed_992_ = lean_unbox_usize(v_stop_989_);
lean_dec(v_stop_989_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_986_, v_as_987_, v_i_boxed_991_, v_stop_boxed_992_, v_b_990_);
lean_dec_ref(v_as_987_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0(lean_object* v_f_994_, lean_object* v_s_995_, lean_object* v_a_996_, lean_object* v_b_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_a_996_);
lean_ctor_set(v___x_998_, 1, v_b_997_);
v___x_999_ = lean_apply_2(v_f_994_, v___x_998_, v_s_995_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(lean_object* v_map_1016_, lean_object* v_init_1017_, lean_object* v_f_1018_){
_start:
{
lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; 
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1019_, 0, v_f_1018_);
lean_inc_ref(v_map_1016_);
v___x_1020_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v___f_1019_, v_map_1016_, v_init_1017_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
return v_a_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___boxed(lean_object* v_map_1022_, lean_object* v_init_1023_, lean_object* v_f_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_1022_, v_init_1023_, v_f_1024_);
lean_dec_ref(v_map_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v_ks_1030_; lean_object* v_vs_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1055_; 
v_ks_1030_ = lean_ctor_get(v_x_1026_, 0);
v_vs_1031_ = lean_ctor_get(v_x_1026_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_1026_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1033_ = v_x_1026_;
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_vs_1031_);
lean_inc(v_ks_1030_);
lean_dec(v_x_1026_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_array_get_size(v_ks_1030_);
v___x_1036_ = lean_nat_dec_lt(v_x_1027_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_dec(v_x_1027_);
v___x_1037_ = lean_array_push(v_ks_1030_, v_x_1028_);
v___x_1038_ = lean_array_push(v_vs_1031_, v_x_1029_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1038_);
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1040_ = v___x_1033_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
lean_object* v_k_x27_1042_; uint8_t v___x_1043_; 
v_k_x27_1042_ = lean_array_fget_borrowed(v_ks_1030_, v_x_1027_);
v___x_1043_ = lean_name_eq(v_x_1028_, v_k_x27_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1045_; 
if (v_isShared_1034_ == 0)
{
v___x_1045_ = v___x_1033_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_ks_1030_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_vs_1031_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_add(v_x_1027_, v___x_1046_);
lean_dec(v_x_1027_);
v_x_1026_ = v___x_1045_;
v_x_1027_ = v___x_1047_;
goto _start;
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1050_ = lean_array_fset(v_ks_1030_, v_x_1027_, v_x_1028_);
v___x_1051_ = lean_array_fset(v_vs_1031_, v_x_1027_, v_x_1029_);
lean_dec(v_x_1027_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1051_);
lean_ctor_set(v___x_1033_, 0, v___x_1050_);
v___x_1053_ = v___x_1033_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_n_1056_, v___x_1059_, v_k_1057_, v_v_1058_);
return v___x_1060_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1061_; uint64_t v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(1723u);
v___x_1062_ = lean_uint64_of_nat(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(lean_object* v_x_1064_, size_t v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1064_) == 0)
{
lean_object* v_es_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v_j_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_es_1069_ = lean_ctor_get(v_x_1064_, 0);
v___x_1070_ = ((size_t)31ULL);
v___x_1071_ = lean_usize_land(v_x_1065_, v___x_1070_);
v_j_1072_ = lean_usize_to_nat(v___x_1071_);
v___x_1073_ = lean_array_get_size(v_es_1069_);
v___x_1074_ = lean_nat_dec_lt(v_j_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec(v_j_1072_);
lean_dec(v_x_1068_);
lean_dec(v_x_1067_);
return v_x_1064_;
}
else
{
lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1113_; 
lean_inc_ref(v_es_1069_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v_x_1064_, 0);
lean_dec(v_unused_1114_);
v___x_1076_ = v_x_1064_;
v_isShared_1077_ = v_isSharedCheck_1113_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v_x_1064_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1113_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_v_1078_; lean_object* v___x_1079_; lean_object* v_xs_x27_1080_; lean_object* v___y_1082_; 
v_v_1078_ = lean_array_fget(v_es_1069_, v_j_1072_);
v___x_1079_ = lean_box(0);
v_xs_x27_1080_ = lean_array_fset(v_es_1069_, v_j_1072_, v___x_1079_);
switch(lean_obj_tag(v_v_1078_))
{
case 0:
{
lean_object* v_key_1087_; lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_key_1087_ = lean_ctor_get(v_v_1078_, 0);
v_val_1088_ = lean_ctor_get(v_v_1078_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_v_1078_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v_v_1078_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_inc(v_key_1087_);
lean_dec(v_v_1078_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_name_eq(v_x_1067_, v_key_1087_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1090_);
v___x_1093_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1087_, v_val_1088_, v_x_1067_, v_x_1068_);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
v___y_1082_ = v___x_1094_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_val_1088_);
lean_dec(v_key_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_x_1068_);
lean_ctor_set(v___x_1090_, 0, v_x_1067_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_x_1067_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_x_1068_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v___y_1082_ = v___x_1096_;
goto v___jp_1081_;
}
}
}
}
case 1:
{
lean_object* v_node_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1111_; 
v_node_1099_ = lean_ctor_get(v_v_1078_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_v_1078_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1101_ = v_v_1078_;
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_node_1099_);
lean_dec(v_v_1078_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1103_ = ((size_t)5ULL);
v___x_1104_ = lean_usize_shift_right(v_x_1065_, v___x_1103_);
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_add(v_x_1066_, v___x_1105_);
v___x_1107_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_node_1099_, v___x_1104_, v___x_1106_, v_x_1067_, v_x_1068_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1107_);
v___x_1109_ = v___x_1101_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v___y_1082_ = v___x_1109_;
goto v___jp_1081_;
}
}
}
default: 
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_x_1067_);
lean_ctor_set(v___x_1112_, 1, v_x_1068_);
v___y_1082_ = v___x_1112_;
goto v___jp_1081_;
}
}
v___jp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_array_fset(v_xs_x27_1080_, v_j_1072_, v___y_1082_);
lean_dec(v_j_1072_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1083_);
v___x_1085_ = v___x_1076_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_ks_1115_; lean_object* v_vs_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1136_; 
v_ks_1115_ = lean_ctor_get(v_x_1064_, 0);
v_vs_1116_ = lean_ctor_get(v_x_1064_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1064_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1118_ = v_x_1064_;
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_vs_1116_);
lean_inc(v_ks_1115_);
lean_dec(v_x_1064_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_ks_1115_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_vs_1116_);
v___x_1121_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v_newNode_1122_; uint8_t v___y_1124_; size_t v___x_1130_; uint8_t v___x_1131_; 
v_newNode_1122_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v___x_1121_, v_x_1067_, v_x_1068_);
v___x_1130_ = ((size_t)7ULL);
v___x_1131_ = lean_usize_dec_le(v___x_1130_, v_x_1066_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1122_);
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = lean_nat_dec_lt(v___x_1132_, v___x_1133_);
lean_dec(v___x_1132_);
v___y_1124_ = v___x_1134_;
goto v___jp_1123_;
}
else
{
v___y_1124_ = v___x_1131_;
goto v___jp_1123_;
}
v___jp_1123_:
{
if (v___y_1124_ == 0)
{
lean_object* v_ks_1125_; lean_object* v_vs_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_ks_1125_ = lean_ctor_get(v_newNode_1122_, 0);
lean_inc_ref(v_ks_1125_);
v_vs_1126_ = lean_ctor_get(v_newNode_1122_, 1);
lean_inc_ref(v_vs_1126_);
lean_dec_ref(v_newNode_1122_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0);
v___x_1129_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_x_1066_, v_ks_1125_, v_vs_1126_, v___x_1127_, v___x_1128_);
lean_dec_ref(v_vs_1126_);
lean_dec_ref(v_ks_1125_);
return v___x_1129_;
}
else
{
return v_newNode_1122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(size_t v_depth_1137_, lean_object* v_keys_1138_, lean_object* v_vals_1139_, lean_object* v_i_1140_, lean_object* v_entries_1141_){
_start:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_array_get_size(v_keys_1138_);
v___x_1143_ = lean_nat_dec_lt(v_i_1140_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_dec(v_i_1140_);
return v_entries_1141_;
}
else
{
lean_object* v_k_1144_; lean_object* v_v_1145_; uint64_t v___y_1147_; 
v_k_1144_ = lean_array_fget_borrowed(v_keys_1138_, v_i_1140_);
v_v_1145_ = lean_array_fget_borrowed(v_vals_1139_, v_i_1140_);
if (lean_obj_tag(v_k_1144_) == 0)
{
uint64_t v___x_1158_; 
v___x_1158_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
v___y_1147_ = v___x_1158_;
goto v___jp_1146_;
}
else
{
uint64_t v_hash_1159_; 
v_hash_1159_ = lean_ctor_get_uint64(v_k_1144_, sizeof(void*)*2);
v___y_1147_ = v_hash_1159_;
goto v___jp_1146_;
}
v___jp_1146_:
{
size_t v_h_1148_; size_t v___x_1149_; lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v_h_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_h_1148_ = lean_uint64_to_usize(v___y_1147_);
v___x_1149_ = ((size_t)5ULL);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_sub(v_depth_1137_, v___x_1151_);
v___x_1153_ = lean_usize_mul(v___x_1149_, v___x_1152_);
v_h_1154_ = lean_usize_shift_right(v_h_1148_, v___x_1153_);
v___x_1155_ = lean_nat_add(v_i_1140_, v___x_1150_);
lean_dec(v_i_1140_);
lean_inc(v_v_1145_);
lean_inc(v_k_1144_);
v___x_1156_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_entries_1141_, v_h_1154_, v_depth_1137_, v_k_1144_, v_v_1145_);
v_i_1140_ = v___x_1155_;
v_entries_1141_ = v___x_1156_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___boxed(lean_object* v_depth_1160_, lean_object* v_keys_1161_, lean_object* v_vals_1162_, lean_object* v_i_1163_, lean_object* v_entries_1164_){
_start:
{
size_t v_depth_boxed_1165_; lean_object* v_res_1166_; 
v_depth_boxed_1165_ = lean_unbox_usize(v_depth_1160_);
lean_dec(v_depth_1160_);
v_res_1166_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_boxed_1165_, v_keys_1161_, v_vals_1162_, v_i_1163_, v_entries_1164_);
lean_dec_ref(v_vals_1162_);
lean_dec_ref(v_keys_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_x_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
size_t v_x_30374__boxed_1172_; size_t v_x_30375__boxed_1173_; lean_object* v_res_1174_; 
v_x_30374__boxed_1172_ = lean_unbox_usize(v_x_1168_);
lean_dec(v_x_1168_);
v_x_30375__boxed_1173_ = lean_unbox_usize(v_x_1169_);
lean_dec(v_x_1169_);
v_res_1174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1167_, v_x_30374__boxed_1172_, v_x_30375__boxed_1173_, v_x_1170_, v_x_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_){
_start:
{
uint64_t v___y_1179_; 
if (lean_obj_tag(v_x_1176_) == 0)
{
uint64_t v___x_1183_; 
v___x_1183_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
v___y_1179_ = v___x_1183_;
goto v___jp_1178_;
}
else
{
uint64_t v_hash_1184_; 
v_hash_1184_ = lean_ctor_get_uint64(v_x_1176_, sizeof(void*)*2);
v___y_1179_ = v_hash_1184_;
goto v___jp_1178_;
}
v___jp_1178_:
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_uint64_to_usize(v___y_1179_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1175_, v___x_1180_, v___x_1181_, v_x_1176_, v_x_1177_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_keys_1185_, lean_object* v_vals_1186_, lean_object* v_i_1187_, lean_object* v_k_1188_){
_start:
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_array_get_size(v_keys_1185_);
v___x_1190_ = lean_nat_dec_lt(v_i_1187_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
lean_dec(v_i_1187_);
v___x_1191_ = lean_box(0);
return v___x_1191_;
}
else
{
lean_object* v_k_x27_1192_; uint8_t v___x_1193_; 
v_k_x27_1192_ = lean_array_fget_borrowed(v_keys_1185_, v_i_1187_);
v___x_1193_ = lean_name_eq(v_k_1188_, v_k_x27_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_i_1187_, v___x_1194_);
lean_dec(v_i_1187_);
v_i_1187_ = v___x_1195_;
goto _start;
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_array_fget_borrowed(v_vals_1186_, v_i_1187_);
lean_dec(v_i_1187_);
lean_inc(v___x_1197_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1199_, lean_object* v_vals_1200_, lean_object* v_i_1201_, lean_object* v_k_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_1199_, v_vals_1200_, v_i_1201_, v_k_1202_);
lean_dec(v_k_1202_);
lean_dec_ref(v_vals_1200_);
lean_dec_ref(v_keys_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(lean_object* v_x_1204_, size_t v_x_1205_, lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
lean_object* v_es_1207_; lean_object* v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; lean_object* v_j_1211_; lean_object* v___x_1212_; 
v_es_1207_ = lean_ctor_get(v_x_1204_, 0);
v___x_1208_ = lean_box(2);
v___x_1209_ = ((size_t)31ULL);
v___x_1210_ = lean_usize_land(v_x_1205_, v___x_1209_);
v_j_1211_ = lean_usize_to_nat(v___x_1210_);
v___x_1212_ = lean_array_get_borrowed(v___x_1208_, v_es_1207_, v_j_1211_);
lean_dec(v_j_1211_);
switch(lean_obj_tag(v___x_1212_))
{
case 0:
{
lean_object* v_key_1213_; lean_object* v_val_1214_; uint8_t v___x_1215_; 
v_key_1213_ = lean_ctor_get(v___x_1212_, 0);
v_val_1214_ = lean_ctor_get(v___x_1212_, 1);
v___x_1215_ = lean_name_eq(v_x_1206_, v_key_1213_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_box(0);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; 
lean_inc(v_val_1214_);
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_val_1214_);
return v___x_1217_;
}
}
case 1:
{
lean_object* v_node_1218_; size_t v___x_1219_; size_t v___x_1220_; 
v_node_1218_ = lean_ctor_get(v___x_1212_, 0);
v___x_1219_ = ((size_t)5ULL);
v___x_1220_ = lean_usize_shift_right(v_x_1205_, v___x_1219_);
v_x_1204_ = v_node_1218_;
v_x_1205_ = v___x_1220_;
goto _start;
}
default: 
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_box(0);
return v___x_1222_;
}
}
}
else
{
lean_object* v_ks_1223_; lean_object* v_vs_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_ks_1223_ = lean_ctor_get(v_x_1204_, 0);
v_vs_1224_ = lean_ctor_get(v_x_1204_, 1);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_ks_1223_, v_vs_1224_, v___x_1225_, v_x_1206_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_1227_, lean_object* v_x_1228_, lean_object* v_x_1229_){
_start:
{
size_t v_x_30573__boxed_1230_; lean_object* v_res_1231_; 
v_x_30573__boxed_1230_ = lean_unbox_usize(v_x_1228_);
lean_dec(v_x_1228_);
v_res_1231_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1227_, v_x_30573__boxed_1230_, v_x_1229_);
lean_dec(v_x_1229_);
lean_dec_ref(v_x_1227_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
uint64_t v___y_1235_; 
if (lean_obj_tag(v_x_1233_) == 0)
{
uint64_t v___x_1238_; 
v___x_1238_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0);
v___y_1235_ = v___x_1238_;
goto v___jp_1234_;
}
else
{
uint64_t v_hash_1239_; 
v_hash_1239_ = lean_ctor_get_uint64(v_x_1233_, sizeof(void*)*2);
v___y_1235_ = v_hash_1239_;
goto v___jp_1234_;
}
v___jp_1234_:
{
size_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_uint64_to_usize(v___y_1235_);
v___x_1237_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1232_, v___x_1236_, v_x_1233_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg___boxed(lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_1240_, v_x_1241_);
lean_dec(v_x_1241_);
lean_dec_ref(v_x_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(lean_object* v_oldCounters_1243_, lean_object* v_x_1244_, lean_object* v_____s_1245_){
_start:
{
lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1248_; 
v_fst_1246_ = lean_ctor_get(v_x_1244_, 0);
lean_inc(v_fst_1246_);
v_snd_1247_ = lean_ctor_get(v_x_1244_, 1);
lean_inc(v_snd_1247_);
lean_dec_ref(v_x_1244_);
v___x_1248_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_oldCounters_1243_, v_fst_1246_);
if (lean_obj_tag(v___x_1248_) == 1)
{
lean_object* v_val_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
v_val_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_val_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v_result_1254_; lean_object* v___x_1256_; 
v___x_1253_ = lean_nat_sub(v_snd_1247_, v_val_1249_);
lean_dec(v_val_1249_);
lean_dec(v_snd_1247_);
v_result_1254_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_1245_, v_fst_1246_, v___x_1253_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_result_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_result_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_result_1259_; lean_object* v___x_1260_; 
lean_dec(v___x_1248_);
v_result_1259_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_____s_1245_, v_fst_1246_, v_snd_1247_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_result_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed(lean_object* v_oldCounters_1261_, lean_object* v_x_1262_, lean_object* v_____s_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0(v_oldCounters_1261_, v_x_1262_, v_____s_1263_);
lean_dec_ref(v_oldCounters_1261_);
return v_res_1264_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v_result_1267_; 
v___x_1266_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__0);
v_result_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_result_1267_, 0, v___x_1266_);
return v_result_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(lean_object* v_newCounters_1268_, lean_object* v_oldCounters_1269_){
_start:
{
lean_object* v___f_1270_; lean_object* v_result_1271_; lean_object* v___x_1272_; 
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1270_, 0, v_oldCounters_1269_);
v_result_1271_ = lean_obj_once(&l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1, &l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1_once, _init_l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___closed__1);
v___x_1272_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_newCounters_1268_, v_result_1271_, v___f_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5___boxed(lean_object* v_newCounters_1273_, lean_object* v_oldCounters_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v_newCounters_1273_, v_oldCounters_1274_);
lean_dec_ref(v_newCounters_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(lean_object* v_f_1276_, lean_object* v_keys_1277_, lean_object* v_vals_1278_, lean_object* v_i_1279_, lean_object* v_acc_1280_){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_array_get_size(v_keys_1277_);
v___x_1282_ = lean_nat_dec_lt(v_i_1279_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec(v_i_1279_);
lean_dec(v_f_1276_);
return v_acc_1280_;
}
else
{
lean_object* v_k_1283_; lean_object* v_v_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_k_1283_ = lean_array_fget_borrowed(v_keys_1277_, v_i_1279_);
v_v_1284_ = lean_array_fget_borrowed(v_vals_1278_, v_i_1279_);
lean_inc(v_f_1276_);
lean_inc(v_v_1284_);
lean_inc(v_k_1283_);
v___x_1285_ = lean_apply_3(v_f_1276_, v_acc_1280_, v_k_1283_, v_v_1284_);
v___x_1286_ = lean_unsigned_to_nat(1u);
v___x_1287_ = lean_nat_add(v_i_1279_, v___x_1286_);
lean_dec(v_i_1279_);
v_i_1279_ = v___x_1287_;
v_acc_1280_ = v___x_1285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg___boxed(lean_object* v_f_1289_, lean_object* v_keys_1290_, lean_object* v_vals_1291_, lean_object* v_i_1292_, lean_object* v_acc_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_1289_, v_keys_1290_, v_vals_1291_, v_i_1292_, v_acc_1293_);
lean_dec_ref(v_vals_1291_);
lean_dec_ref(v_keys_1290_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(lean_object* v_f_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1296_) == 0)
{
lean_object* v_es_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_es_1298_ = lean_ctor_get(v_x_1296_, 0);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_array_get_size(v_es_1298_);
v___x_1301_ = lean_nat_dec_lt(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v_f_1295_);
return v_x_1297_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_le(v___x_1300_, v___x_1300_);
if (v___x_1302_ == 0)
{
if (v___x_1301_ == 0)
{
lean_dec(v_f_1295_);
return v_x_1297_;
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = lean_usize_of_nat(v___x_1300_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_1295_, v_es_1298_, v___x_1303_, v___x_1304_, v_x_1297_);
return v___x_1305_;
}
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1300_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_1295_, v_es_1298_, v___x_1306_, v___x_1307_, v_x_1297_);
return v___x_1308_;
}
}
}
else
{
lean_object* v_ks_1309_; lean_object* v_vs_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_ks_1309_ = lean_ctor_get(v_x_1296_, 0);
v_vs_1310_ = lean_ctor_get(v_x_1296_, 1);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_1295_, v_ks_1309_, v_vs_1310_, v___x_1311_, v_x_1297_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(lean_object* v_f_1313_, lean_object* v_as_1314_, size_t v_i_1315_, size_t v_stop_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v___y_1319_; uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_eq(v_i_1315_, v_stop_1316_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_array_uget_borrowed(v_as_1314_, v_i_1315_);
switch(lean_obj_tag(v___x_1324_))
{
case 0:
{
lean_object* v_key_1325_; lean_object* v_val_1326_; lean_object* v___x_1327_; 
v_key_1325_ = lean_ctor_get(v___x_1324_, 0);
v_val_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_f_1313_);
lean_inc(v_val_1326_);
lean_inc(v_key_1325_);
v___x_1327_ = lean_apply_3(v_f_1313_, v_b_1317_, v_key_1325_, v_val_1326_);
v___y_1319_ = v___x_1327_;
goto v___jp_1318_;
}
case 1:
{
lean_object* v_node_1328_; lean_object* v___x_1329_; 
v_node_1328_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_f_1313_);
v___x_1329_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1313_, v_node_1328_, v_b_1317_);
v___y_1319_ = v___x_1329_;
goto v___jp_1318_;
}
default: 
{
v___y_1319_ = v_b_1317_;
goto v___jp_1318_;
}
}
}
else
{
lean_dec(v_f_1313_);
return v_b_1317_;
}
v___jp_1318_:
{
size_t v___x_1320_; size_t v___x_1321_; 
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1315_, v___x_1320_);
v_i_1315_ = v___x_1321_;
v_b_1317_ = v___y_1319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg___boxed(lean_object* v_f_1330_, lean_object* v_as_1331_, lean_object* v_i_1332_, lean_object* v_stop_1333_, lean_object* v_b_1334_){
_start:
{
size_t v_i_boxed_1335_; size_t v_stop_boxed_1336_; lean_object* v_res_1337_; 
v_i_boxed_1335_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_stop_boxed_1336_ = lean_unbox_usize(v_stop_1333_);
lean_dec(v_stop_1333_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_1330_, v_as_1331_, v_i_boxed_1335_, v_stop_boxed_1336_, v_b_1334_);
lean_dec_ref(v_as_1331_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg___boxed(lean_object* v_f_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1338_, v_x_1339_, v_x_1340_);
lean_dec_ref(v_x_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0(lean_object* v_f_1342_, lean_object* v_x1_1343_, lean_object* v_x2_1344_, lean_object* v_x3_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_apply_3(v_f_1342_, v_x1_1343_, v_x2_1344_, v_x3_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(lean_object* v_map_1347_, lean_object* v_f_1348_, lean_object* v_init_1349_){
_start:
{
lean_object* v___f_1350_; lean_object* v___x_1351_; 
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1350_, 0, v_f_1348_);
v___x_1351_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v___f_1350_, v_map_1347_, v_init_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg___boxed(lean_object* v_map_1352_, lean_object* v_f_1353_, lean_object* v_init_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_1352_, v_f_1353_, v_init_1354_);
lean_dec_ref(v_map_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___lam__0(lean_object* v_ps_1356_, lean_object* v_k_1357_, lean_object* v_v_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_k_1357_);
lean_ctor_set(v___x_1359_, 1, v_v_1358_);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v_ps_1356_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(lean_object* v_m_1362_){
_start:
{
lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___f_1363_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___closed__0));
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_m_1362_, v___f_1363_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg___boxed(lean_object* v_m_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_1366_);
lean_dec_ref(v_m_1366_);
return v_res_1367_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2));
v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(1);
v___x_1375_ = l_Lean_MessageData_ofFormat(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8));
v___x_1383_ = l_Lean_MessageData_ofFormat(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11));
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1389_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__14);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(uint8_t v_a_1394_, lean_object* v_kind_1395_, lean_object* v___x_1396_, lean_object* v_a_1397_, uint8_t v___x_1398_, lean_object* v_diag_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; uint8_t v___y_1436_; lean_object* v___x_1454_; lean_object* v_fileName_1455_; lean_object* v_fileMap_1456_; lean_object* v_options_1457_; lean_object* v_currRecDepth_1458_; lean_object* v_ref_1459_; lean_object* v_currNamespace_1460_; lean_object* v_openDecls_1461_; lean_object* v_initHeartbeats_1462_; lean_object* v_maxHeartbeats_1463_; lean_object* v_quotContext_1464_; lean_object* v_currMacroScope_1465_; lean_object* v_cancelTk_x3f_1466_; uint8_t v_suppressElabErrors_1467_; lean_object* v_inheritedTraceOptions_1468_; lean_object* v_env_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v_fileName_1474_; lean_object* v_fileMap_1475_; lean_object* v_currRecDepth_1476_; lean_object* v_ref_1477_; lean_object* v_currNamespace_1478_; lean_object* v_openDecls_1479_; lean_object* v_initHeartbeats_1480_; lean_object* v_maxHeartbeats_1481_; lean_object* v_quotContext_1482_; lean_object* v_currMacroScope_1483_; lean_object* v_cancelTk_x3f_1484_; uint8_t v_suppressElabErrors_1485_; lean_object* v_inheritedTraceOptions_1486_; lean_object* v___y_1487_; uint8_t v___y_1527_; uint8_t v___x_1548_; 
v___x_1454_ = lean_st_ref_get(v___y_1403_);
v_fileName_1455_ = lean_ctor_get(v___y_1402_, 0);
v_fileMap_1456_ = lean_ctor_get(v___y_1402_, 1);
v_options_1457_ = lean_ctor_get(v___y_1402_, 2);
v_currRecDepth_1458_ = lean_ctor_get(v___y_1402_, 3);
v_ref_1459_ = lean_ctor_get(v___y_1402_, 5);
v_currNamespace_1460_ = lean_ctor_get(v___y_1402_, 6);
v_openDecls_1461_ = lean_ctor_get(v___y_1402_, 7);
v_initHeartbeats_1462_ = lean_ctor_get(v___y_1402_, 8);
v_maxHeartbeats_1463_ = lean_ctor_get(v___y_1402_, 9);
v_quotContext_1464_ = lean_ctor_get(v___y_1402_, 10);
v_currMacroScope_1465_ = lean_ctor_get(v___y_1402_, 11);
v_cancelTk_x3f_1466_ = lean_ctor_get(v___y_1402_, 12);
v_suppressElabErrors_1467_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1468_ = lean_ctor_get(v___y_1402_, 13);
v_env_1469_ = lean_ctor_get(v___x_1454_, 0);
lean_inc_ref(v_env_1469_);
lean_dec(v___x_1454_);
v___x_1470_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1457_);
v___x_1471_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_options_1457_, v___x_1470_, v_a_1394_);
v___x_1472_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v___x_1471_, v___x_1470_);
v___x_1548_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1469_);
lean_dec_ref(v_env_1469_);
if (v___x_1548_ == 0)
{
if (v___x_1472_ == 0)
{
v_fileName_1474_ = v_fileName_1455_;
v_fileMap_1475_ = v_fileMap_1456_;
v_currRecDepth_1476_ = v_currRecDepth_1458_;
v_ref_1477_ = v_ref_1459_;
v_currNamespace_1478_ = v_currNamespace_1460_;
v_openDecls_1479_ = v_openDecls_1461_;
v_initHeartbeats_1480_ = v_initHeartbeats_1462_;
v_maxHeartbeats_1481_ = v_maxHeartbeats_1463_;
v_quotContext_1482_ = v_quotContext_1464_;
v_currMacroScope_1483_ = v_currMacroScope_1465_;
v_cancelTk_x3f_1484_ = v_cancelTk_x3f_1466_;
v_suppressElabErrors_1485_ = v_suppressElabErrors_1467_;
v_inheritedTraceOptions_1486_ = v_inheritedTraceOptions_1468_;
v___y_1487_ = v___y_1403_;
goto v___jp_1473_;
}
else
{
v___y_1527_ = v___x_1548_;
goto v___jp_1526_;
}
}
else
{
v___y_1527_ = v___x_1472_;
goto v___jp_1526_;
}
v___jp_1405_:
{
if (v___y_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec_ref(v___y_1406_);
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1406_);
return v___x_1410_;
}
}
v___jp_1411_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1415_ = l_Lean_stringToMessageData(v_kind_1395_);
v___x_1416_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
lean_inc_ref(v___y_1414_);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___y_1414_);
v___x_1419_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4);
v___x_1422_ = l_Lean_MessageData_joinSep(v___y_1413_, v___x_1421_);
v___x_1423_ = l_Lean_indentD(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1420_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Lean_Exception_toMessageData(v___y_1412_);
v___x_1428_ = l_Lean_indentD(v___x_1427_);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1426_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
v___jp_1432_:
{
if (v___y_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_diag_1439_; lean_object* v_unfoldCounter_1440_; lean_object* v_env_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1437_ = lean_st_ref_get(v___y_1401_);
v___x_1438_ = lean_st_ref_get(v___y_1434_);
v_diag_1439_ = lean_ctor_get(v___x_1437_, 4);
lean_inc_ref(v_diag_1439_);
lean_dec(v___x_1437_);
v_unfoldCounter_1440_ = lean_ctor_get(v_diag_1439_, 0);
lean_inc_ref(v_unfoldCounter_1440_);
lean_dec_ref(v_diag_1439_);
v_env_1441_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1441_);
lean_dec(v___x_1438_);
v___x_1442_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v___y_1435_, v_unfoldCounter_1440_);
lean_dec_ref(v___y_1435_);
v___x_1443_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v___x_1442_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = lean_mk_empty_array_with_capacity(v___x_1396_);
v___x_1445_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(v_env_1441_, v___x_1443_, v___x_1444_);
v___x_1446_ = l_List_isEmpty___redArg(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3));
v___x_1448_ = lean_string_dec_eq(v_kind_1395_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9);
v___y_1412_ = v___y_1433_;
v___y_1413_ = v___x_1445_;
v___y_1414_ = v___x_1449_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12);
v___y_1412_ = v___y_1433_;
v___y_1413_ = v___x_1445_;
v___y_1414_ = v___x_1450_;
goto v___jp_1411_;
}
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v___x_1445_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v_kind_1395_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
else
{
lean_object* v___x_1453_; 
lean_dec_ref(v___y_1435_);
lean_dec_ref(v_kind_1395_);
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1433_);
return v___x_1453_;
}
}
v___jp_1473_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = l_Lean_maxRecDepth;
v___x_1489_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v___x_1471_, v___x_1488_);
lean_inc_ref(v_inheritedTraceOptions_1486_);
lean_inc(v_cancelTk_x3f_1484_);
lean_inc(v_currMacroScope_1483_);
lean_inc(v_quotContext_1482_);
lean_inc(v_maxHeartbeats_1481_);
lean_inc(v_initHeartbeats_1480_);
lean_inc(v_openDecls_1479_);
lean_inc(v_currNamespace_1478_);
lean_inc(v_ref_1477_);
lean_inc(v_currRecDepth_1476_);
lean_inc_ref(v_fileMap_1475_);
lean_inc_ref(v_fileName_1474_);
v___x_1490_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1490_, 0, v_fileName_1474_);
lean_ctor_set(v___x_1490_, 1, v_fileMap_1475_);
lean_ctor_set(v___x_1490_, 2, v___x_1471_);
lean_ctor_set(v___x_1490_, 3, v_currRecDepth_1476_);
lean_ctor_set(v___x_1490_, 4, v___x_1489_);
lean_ctor_set(v___x_1490_, 5, v_ref_1477_);
lean_ctor_set(v___x_1490_, 6, v_currNamespace_1478_);
lean_ctor_set(v___x_1490_, 7, v_openDecls_1479_);
lean_ctor_set(v___x_1490_, 8, v_initHeartbeats_1480_);
lean_ctor_set(v___x_1490_, 9, v_maxHeartbeats_1481_);
lean_ctor_set(v___x_1490_, 10, v_quotContext_1482_);
lean_ctor_set(v___x_1490_, 11, v_currMacroScope_1483_);
lean_ctor_set(v___x_1490_, 12, v_cancelTk_x3f_1484_);
lean_ctor_set(v___x_1490_, 13, v_inheritedTraceOptions_1486_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*14, v___x_1472_);
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*14 + 1, v_suppressElabErrors_1485_);
lean_inc_ref(v_a_1397_);
v___x_1491_ = l_Lean_Meta_check(v_a_1397_, v___x_1398_, v___y_1400_, v___y_1401_, v___x_1490_, v___y_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_mctx_1494_; lean_object* v_cache_1495_; lean_object* v_zetaDeltaFVarIds_1496_; lean_object* v_postponed_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref_known(v___x_1491_, 1);
v___x_1492_ = lean_st_ref_get(v___y_1401_);
v___x_1493_ = lean_st_ref_take(v___y_1401_);
v_mctx_1494_ = lean_ctor_get(v___x_1493_, 0);
v_cache_1495_ = lean_ctor_get(v___x_1493_, 1);
v_zetaDeltaFVarIds_1496_ = lean_ctor_get(v___x_1493_, 2);
v_postponed_1497_ = lean_ctor_get(v___x_1493_, 3);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1493_, 4);
lean_dec(v_unused_1522_);
v___x_1499_ = v___x_1493_;
v_isShared_1500_ = v_isSharedCheck_1521_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_postponed_1497_);
lean_inc(v_zetaDeltaFVarIds_1496_);
lean_inc(v_cache_1495_);
lean_inc(v_mctx_1494_);
lean_dec(v___x_1493_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1521_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 4, v_diag_1399_);
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_mctx_1494_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_cache_1495_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_zetaDeltaFVarIds_1496_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_postponed_1497_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_diag_1399_);
v___x_1502_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_st_ref_set(v___y_1401_, v___x_1502_);
v___x_1504_ = 5;
v___x_1505_ = l_Lean_Meta_check(v_a_1397_, v___x_1504_, v___y_1400_, v___y_1401_, v___x_1490_, v___y_1487_);
lean_dec_ref_known(v___x_1490_, 14);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v___x_1492_);
lean_dec_ref(v_kind_1395_);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v___x_1505_, 0);
lean_dec(v_unused_1514_);
v___x_1507_ = v___x_1505_;
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v___x_1505_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1509_);
v___x_1511_ = v___x_1507_;
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
else
{
lean_object* v_diag_1515_; lean_object* v_a_1516_; lean_object* v_unfoldCounter_1517_; uint8_t v___x_1518_; 
v_diag_1515_ = lean_ctor_get(v___x_1492_, 4);
lean_inc_ref(v_diag_1515_);
lean_dec(v___x_1492_);
v_a_1516_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1505_, 1);
v_unfoldCounter_1517_ = lean_ctor_get(v_diag_1515_, 0);
lean_inc_ref(v_unfoldCounter_1517_);
lean_dec_ref(v_diag_1515_);
v___x_1518_ = l_Lean_Exception_isInterrupt(v_a_1516_);
if (v___x_1518_ == 0)
{
uint8_t v___x_1519_; 
lean_inc(v_a_1516_);
v___x_1519_ = l_Lean_Exception_isRuntime(v_a_1516_);
v___y_1433_ = v_a_1516_;
v___y_1434_ = v___y_1487_;
v___y_1435_ = v_unfoldCounter_1517_;
v___y_1436_ = v___x_1519_;
goto v___jp_1432_;
}
else
{
v___y_1433_ = v_a_1516_;
v___y_1434_ = v___y_1487_;
v___y_1435_ = v_unfoldCounter_1517_;
v___y_1436_ = v___x_1518_;
goto v___jp_1432_;
}
}
}
}
}
else
{
lean_object* v_a_1523_; uint8_t v___x_1524_; 
lean_dec_ref_known(v___x_1490_, 14);
lean_dec_ref(v_diag_1399_);
lean_dec_ref(v_a_1397_);
lean_dec_ref(v_kind_1395_);
v_a_1523_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1524_ = l_Lean_Exception_isInterrupt(v_a_1523_);
if (v___x_1524_ == 0)
{
uint8_t v___x_1525_; 
lean_inc(v_a_1523_);
v___x_1525_ = l_Lean_Exception_isRuntime(v_a_1523_);
v___y_1406_ = v_a_1523_;
v___y_1407_ = v___x_1525_;
goto v___jp_1405_;
}
else
{
v___y_1406_ = v_a_1523_;
v___y_1407_ = v___x_1524_;
goto v___jp_1405_;
}
}
}
v___jp_1526_:
{
if (v___y_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v_env_1529_; lean_object* v_nextMacroScope_1530_; lean_object* v_ngen_1531_; lean_object* v_auxDeclNGen_1532_; lean_object* v_traceState_1533_; lean_object* v_messages_1534_; lean_object* v_infoState_1535_; lean_object* v_snapshotTasks_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1546_; 
v___x_1528_ = lean_st_ref_take(v___y_1403_);
v_env_1529_ = lean_ctor_get(v___x_1528_, 0);
v_nextMacroScope_1530_ = lean_ctor_get(v___x_1528_, 1);
v_ngen_1531_ = lean_ctor_get(v___x_1528_, 2);
v_auxDeclNGen_1532_ = lean_ctor_get(v___x_1528_, 3);
v_traceState_1533_ = lean_ctor_get(v___x_1528_, 4);
v_messages_1534_ = lean_ctor_get(v___x_1528_, 6);
v_infoState_1535_ = lean_ctor_get(v___x_1528_, 7);
v_snapshotTasks_1536_ = lean_ctor_get(v___x_1528_, 8);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1528_, 5);
lean_dec(v_unused_1547_);
v___x_1538_ = v___x_1528_;
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_snapshotTasks_1536_);
lean_inc(v_infoState_1535_);
lean_inc(v_messages_1534_);
lean_inc(v_traceState_1533_);
lean_inc(v_auxDeclNGen_1532_);
lean_inc(v_ngen_1531_);
lean_inc(v_nextMacroScope_1530_);
lean_inc(v_env_1529_);
lean_dec(v___x_1528_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = l_Lean_Kernel_enableDiag(v_env_1529_, v___x_1472_);
v___x_1541_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__15);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 5, v___x_1541_);
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1543_ = v___x_1538_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_nextMacroScope_1530_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_ngen_1531_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_auxDeclNGen_1532_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_traceState_1533_);
lean_ctor_set(v_reuseFailAlloc_1545_, 5, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1545_, 6, v_messages_1534_);
lean_ctor_set(v_reuseFailAlloc_1545_, 7, v_infoState_1535_);
lean_ctor_set(v_reuseFailAlloc_1545_, 8, v_snapshotTasks_1536_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_st_ref_set(v___y_1403_, v___x_1543_);
v_fileName_1474_ = v_fileName_1455_;
v_fileMap_1475_ = v_fileMap_1456_;
v_currRecDepth_1476_ = v_currRecDepth_1458_;
v_ref_1477_ = v_ref_1459_;
v_currNamespace_1478_ = v_currNamespace_1460_;
v_openDecls_1479_ = v_openDecls_1461_;
v_initHeartbeats_1480_ = v_initHeartbeats_1462_;
v_maxHeartbeats_1481_ = v_maxHeartbeats_1463_;
v_quotContext_1482_ = v_quotContext_1464_;
v_currMacroScope_1483_ = v_currMacroScope_1465_;
v_cancelTk_x3f_1484_ = v_cancelTk_x3f_1466_;
v_suppressElabErrors_1485_ = v_suppressElabErrors_1467_;
v_inheritedTraceOptions_1486_ = v_inheritedTraceOptions_1468_;
v___y_1487_ = v___y_1403_;
goto v___jp_1473_;
}
}
}
else
{
v_fileName_1474_ = v_fileName_1455_;
v_fileMap_1475_ = v_fileMap_1456_;
v_currRecDepth_1476_ = v_currRecDepth_1458_;
v_ref_1477_ = v_ref_1459_;
v_currNamespace_1478_ = v_currNamespace_1460_;
v_openDecls_1479_ = v_openDecls_1461_;
v_initHeartbeats_1480_ = v_initHeartbeats_1462_;
v_maxHeartbeats_1481_ = v_maxHeartbeats_1463_;
v_quotContext_1482_ = v_quotContext_1464_;
v_currMacroScope_1483_ = v_currMacroScope_1465_;
v_cancelTk_x3f_1484_ = v_cancelTk_x3f_1466_;
v_suppressElabErrors_1485_ = v_suppressElabErrors_1467_;
v_inheritedTraceOptions_1486_ = v_inheritedTraceOptions_1468_;
v___y_1487_ = v___y_1403_;
goto v___jp_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed(lean_object* v_a_1549_, lean_object* v_kind_1550_, lean_object* v___x_1551_, lean_object* v_a_1552_, lean_object* v___x_1553_, lean_object* v_diag_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_a_30832__boxed_1560_; uint8_t v___x_30835__boxed_1561_; lean_object* v_res_1562_; 
v_a_30832__boxed_1560_ = lean_unbox(v_a_1549_);
v___x_30835__boxed_1561_ = lean_unbox(v___x_1553_);
v_res_1562_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(v_a_30832__boxed_1560_, v_kind_1550_, v___x_1551_, v_a_1552_, v___x_30835__boxed_1561_, v_diag_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___x_1551_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(uint8_t v_a_1568_, lean_object* v_kind_1569_, lean_object* v_as_x27_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
if (lean_obj_tag(v_as_x27_1570_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v_kind_1569_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_b_1571_);
return v___x_1577_;
}
else
{
lean_object* v_head_1578_; lean_object* v_tail_1579_; lean_object* v___x_1580_; lean_object* v_mctx_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_a_1585_; lean_object* v___x_1590_; 
lean_dec_ref(v_b_1571_);
v_head_1578_ = lean_ctor_get(v_as_x27_1570_, 0);
v_tail_1579_ = lean_ctor_get(v_as_x27_1570_, 1);
v___x_1580_ = lean_st_ref_get(v___y_1573_);
v_mctx_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc_ref(v_mctx_1581_);
lean_dec(v___x_1580_);
v___x_1582_ = lean_box(0);
v___x_1583_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0));
v___x_1590_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1581_, v_head_1578_);
lean_dec_ref(v_mctx_1581_);
if (lean_obj_tag(v___x_1590_) == 1)
{
lean_object* v_val_1591_; lean_object* v_lctx_1592_; lean_object* v_type_1593_; lean_object* v___x_1594_; lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v_diag_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v_lctx_1592_ = lean_ctor_get(v_val_1591_, 1);
lean_inc_ref(v_lctx_1592_);
v_type_1593_ = lean_ctor_get(v_val_1591_, 2);
lean_inc_ref(v_type_1593_);
lean_dec(v_val_1591_);
v___x_1594_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_1593_, v___y_1573_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = lean_st_ref_get(v___y_1573_);
v_diag_1597_ = lean_ctor_get(v___x_1596_, 4);
lean_inc_ref_n(v_diag_1597_, 2);
lean_dec(v___x_1596_);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1));
v___x_1600_ = 1;
v___x_1601_ = lean_box(v_a_1568_);
v___x_1602_ = lean_box(v___x_1600_);
lean_inc_ref(v_kind_1569_);
v___f_1603_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1603_, 0, v___x_1601_);
lean_closure_set(v___f_1603_, 1, v_kind_1569_);
lean_closure_set(v___f_1603_, 2, v___x_1598_);
lean_closure_set(v___f_1603_, 3, v_a_1595_);
lean_closure_set(v___f_1603_, 4, v___x_1602_);
lean_closure_set(v___f_1603_, 5, v_diag_1597_);
v___x_1604_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_1592_, v___x_1599_, v___f_1603_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1606_; lean_object* v_mctx_1607_; lean_object* v_cache_1608_; lean_object* v_zetaDeltaFVarIds_1609_; lean_object* v_postponed_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1618_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = lean_st_ref_take(v___y_1573_);
v_mctx_1607_ = lean_ctor_get(v___x_1606_, 0);
v_cache_1608_ = lean_ctor_get(v___x_1606_, 1);
v_zetaDeltaFVarIds_1609_ = lean_ctor_get(v___x_1606_, 2);
v_postponed_1610_ = lean_ctor_get(v___x_1606_, 3);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v___x_1606_, 4);
lean_dec(v_unused_1619_);
v___x_1612_ = v___x_1606_;
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_postponed_1610_);
lean_inc(v_zetaDeltaFVarIds_1609_);
lean_inc(v_cache_1608_);
lean_inc(v_mctx_1607_);
lean_dec(v___x_1606_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 4, v_diag_1597_);
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_mctx_1607_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_cache_1608_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_zetaDeltaFVarIds_1609_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_postponed_1610_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_diag_1597_);
v___x_1615_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_st_ref_set(v___y_1573_, v___x_1615_);
v_a_1585_ = v_a_1605_;
goto v___jp_1584_;
}
}
}
else
{
lean_dec_ref(v_diag_1597_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1620_; 
v_a_1620_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1604_, 1);
v_a_1585_ = v_a_1620_;
goto v___jp_1584_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_kind_1569_);
v_a_1621_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1604_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1604_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
else
{
lean_dec(v___x_1590_);
v_as_x27_1570_ = v_tail_1579_;
v_b_1571_ = v___x_1583_;
goto _start;
}
v___jp_1584_:
{
if (lean_obj_tag(v_a_1585_) == 1)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v_kind_1569_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_a_1585_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v___x_1582_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
else
{
lean_dec(v_a_1585_);
v_as_x27_1570_ = v_tail_1579_;
v_b_1571_ = v___x_1583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___boxed(lean_object* v_a_1630_, lean_object* v_kind_1631_, lean_object* v_as_x27_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v_a_31095__boxed_1639_; lean_object* v_res_1640_; 
v_a_31095__boxed_1639_ = lean_unbox(v_a_1630_);
v_res_1640_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_31095__boxed_1639_, v_kind_1631_, v_as_x27_1632_, v_b_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_as_x27_1632_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(uint8_t v_a_1641_, lean_object* v_kind_1642_, lean_object* v_goals_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0));
v___x_1651_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_1641_, v_kind_1642_, v_goals_1643_, v___x_1650_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1664_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1664_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1664_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_fst_1656_; 
v_fst_1656_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_fst_1656_);
lean_dec(v_a_1652_);
if (lean_obj_tag(v_fst_1656_) == 0)
{
lean_object* v___x_1658_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1649_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1649_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v_val_1660_; lean_object* v___x_1662_; 
v_val_1660_ = lean_ctor_get(v_fst_1656_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v_fst_1656_, 1);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v_val_1660_);
v___x_1662_ = v___x_1654_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_val_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1651_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1651_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed(lean_object* v_a_1673_, lean_object* v_kind_1674_, lean_object* v_goals_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
uint8_t v_a_31213__boxed_1681_; lean_object* v_res_1682_; 
v_a_31213__boxed_1681_ = lean_unbox(v_a_1673_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(v_a_31213__boxed_1681_, v_kind_1674_, v_goals_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v_goals_1675_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(uint8_t v_a_1683_, lean_object* v_val_1684_, lean_object* v_as_1685_, size_t v_sz_1686_, size_t v_i_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_lt(v_i_1687_, v_sz_1686_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_dec(v_val_1684_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_b_1688_);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___f_1700_; lean_object* v_a_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1694_ = lean_box(v_a_1683_);
v___f_1695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1695_, 0, v___x_1694_);
v___x_1696_ = lean_box(v_a_1683_);
v___f_1697_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1697_, 0, v___x_1696_);
v___x_1698_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1699_ = lean_box(v_a_1683_);
lean_inc(v_val_1684_);
v___f_1700_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1700_, 0, v_val_1684_);
lean_closure_set(v___f_1700_, 1, v___x_1699_);
lean_closure_set(v___f_1700_, 2, v___x_1698_);
lean_closure_set(v___f_1700_, 3, v___f_1695_);
v_a_1701_ = lean_array_uget_borrowed(v_as_1685_, v_i_1687_);
v___x_1702_ = lean_box(0);
lean_inc(v_a_1701_);
v___x_1703_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___f_1697_, v___f_1700_, v___x_1702_, v_a_1701_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; size_t v___x_1705_; size_t v___x_1706_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1704_ = lean_box(0);
v___x_1705_ = ((size_t)1ULL);
v___x_1706_ = lean_usize_add(v_i_1687_, v___x_1705_);
v_i_1687_ = v___x_1706_;
v_b_1688_ = v___x_1704_;
goto _start;
}
else
{
lean_dec(v_val_1684_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___boxed(lean_object* v_a_1708_, lean_object* v_val_1709_, lean_object* v_as_1710_, lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v_a_31278__boxed_1717_; size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_a_31278__boxed_1717_ = lean_unbox(v_a_1708_);
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v_a_31278__boxed_1717_, v_val_1709_, v_as_1710_, v_sz_boxed_1718_, v_i_boxed_1719_, v_b_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v_as_1710_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object* v___cmdStx_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1756_; 
v___x_1725_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1726_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_1725_, v___y_1723_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1756_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1756_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_unbox(v_a_1727_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec(v_a_1727_);
v___x_1732_ = lean_box(0);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1732_);
v___x_1734_ = v___x_1729_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
else
{
lean_object* v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v_infoState_1740_; lean_object* v_trees_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; size_t v_sz_1744_; size_t v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; 
lean_del_object(v___x_1729_);
v___x_1736_ = lean_st_ref_get(v___y_1723_);
v___x_1737_ = 0;
v___x_1738_ = lean_box(v___x_1737_);
v___x_1739_ = lean_st_mk_ref(v___x_1738_);
v_infoState_1740_ = lean_ctor_get(v___x_1736_, 8);
lean_inc_ref(v_infoState_1740_);
lean_dec(v___x_1736_);
v_trees_1741_ = lean_ctor_get(v_infoState_1740_, 2);
lean_inc_ref(v_trees_1741_);
lean_dec_ref(v_infoState_1740_);
v___x_1742_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1741_);
lean_dec_ref(v_trees_1741_);
v___x_1743_ = lean_box(0);
v_sz_1744_ = lean_array_size(v___x_1742_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = lean_unbox(v_a_1727_);
lean_dec(v_a_1727_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v___x_1746_, v___x_1739_, v___x_1742_, v_sz_1744_, v___x_1745_, v___x_1743_, v___y_1722_, v___y_1723_);
lean_dec_ref(v___x_1742_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1747_, 0);
lean_dec(v_unused_1755_);
v___x_1749_ = v___x_1747_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_dec(v___x_1747_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1743_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1743_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object* v___cmdStx_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(v___cmdStx_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___cmdStx_1757_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object* v_opt_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1770_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object* v_opt_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_opt_1775_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object* v_00_u03b2_1780_, lean_object* v_m_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object* v_00_u03b2_1783_, lean_object* v_m_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_00_u03b2_1783_, v_m_1784_);
lean_dec_ref(v_m_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(uint8_t v_a_1786_, lean_object* v_kind_1787_, lean_object* v_as_1788_, lean_object* v_as_x27_1789_, lean_object* v_b_1790_, lean_object* v_a_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_1786_, v_kind_1787_, v_as_x27_1789_, v_b_1790_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object* v_a_1798_, lean_object* v_kind_1799_, lean_object* v_as_1800_, lean_object* v_as_x27_1801_, lean_object* v_b_1802_, lean_object* v_a_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v_a_31457__boxed_1809_; lean_object* v_res_1810_; 
v_a_31457__boxed_1809_ = lean_unbox(v_a_1798_);
v_res_1810_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_a_31457__boxed_1809_, v_kind_1799_, v_as_1800_, v_as_x27_1801_, v_b_1802_, v_a_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_as_x27_1801_);
lean_dec(v_as_1800_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(lean_object* v_00_u03b2_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_1812_, v_x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(v_00_u03b2_1815_, v_x_1816_, v_x_1817_);
lean_dec(v_x_1817_);
lean_dec_ref(v_x_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7(lean_object* v_00_u03b2_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_x_1820_, v_x_1821_, v_x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(lean_object* v_00_u03c3_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_map_1826_, lean_object* v_init_1827_, lean_object* v_f_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_1826_, v_init_1827_, v_f_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_map_1832_, lean_object* v_init_1833_, lean_object* v_f_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(v_00_u03c3_1830_, v_00_u03b2_1831_, v_map_1832_, v_init_1833_, v_f_1834_);
lean_dec_ref(v_map_1832_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(lean_object* v_00_u03c3_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_map_1838_, lean_object* v_f_1839_, lean_object* v_init_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_1838_, v_f_1839_, v_init_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___boxed(lean_object* v_00_u03c3_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_map_1844_, lean_object* v_f_1845_, lean_object* v_init_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(v_00_u03c3_1842_, v_00_u03b2_1843_, v_map_1844_, v_f_1845_, v_init_1846_);
lean_dec_ref(v_map_1844_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(lean_object* v_00_u03b1_1848_, lean_object* v_msg_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_1849_, v___y_1850_, v___y_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___boxed(lean_object* v_00_u03b1_1854_, lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(v_00_u03b1_1854_, v_msg_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(lean_object* v_00_u03b1_1860_, lean_object* v_preNode_1861_, lean_object* v_postNode_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_1861_, v_postNode_1862_, v_x_1863_, v_x_1864_, v___y_1865_, v___y_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___boxed(lean_object* v_00_u03b1_1869_, lean_object* v_preNode_1870_, lean_object* v_postNode_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(v_00_u03b1_1869_, v_preNode_1870_, v_postNode_1871_, v_x_1872_, v_x_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1878_, lean_object* v_x_1879_, size_t v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1879_, v_x_1880_, v_x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
size_t v_x_31529__boxed_1887_; lean_object* v_res_1888_; 
v_x_31529__boxed_1887_ = lean_unbox_usize(v_x_1885_);
lean_dec(v_x_1885_);
v_res_1888_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(v_00_u03b2_1883_, v_x_1884_, v_x_31529__boxed_1887_, v_x_1886_);
lean_dec(v_x_1886_);
lean_dec_ref(v_x_1884_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_1889_, lean_object* v_x_1890_, size_t v_x_1891_, size_t v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1890_, v_x_1891_, v_x_1892_, v_x_1893_, v_x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
size_t v_x_31540__boxed_1902_; size_t v_x_31541__boxed_1903_; lean_object* v_res_1904_; 
v_x_31540__boxed_1902_ = lean_unbox_usize(v_x_1898_);
lean_dec(v_x_1898_);
v_x_31541__boxed_1903_ = lean_unbox_usize(v_x_1899_);
lean_dec(v_x_1899_);
v_res_1904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(v_00_u03b2_1896_, v_x_1897_, v_x_31540__boxed_1902_, v_x_31541__boxed_1903_, v_x_1900_, v_x_1901_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12___redArg(lean_object* v_map_1905_, lean_object* v_f_1906_, lean_object* v_init_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_1906_, v_map_1905_, v_init_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12(lean_object* v_00_u03c3_1909_, lean_object* v_00_u03c3_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_map_1912_, lean_object* v_f_1913_, lean_object* v_init_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_1913_, v_map_1912_, v_init_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(lean_object* v_map_1916_, lean_object* v_f_1917_, lean_object* v_init_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1917_, v_map_1916_, v_init_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_map_1920_, lean_object* v_f_1921_, lean_object* v_init_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(v_map_1920_, v_f_1921_, v_init_1922_);
lean_dec_ref(v_map_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(lean_object* v_00_u03c3_1924_, lean_object* v_00_u03b2_1925_, lean_object* v_map_1926_, lean_object* v_f_1927_, lean_object* v_init_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1927_, v_map_1926_, v_init_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03c3_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_map_1932_, lean_object* v_f_1933_, lean_object* v_init_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(v_00_u03c3_1930_, v_00_u03b2_1931_, v_map_1932_, v_f_1933_, v_init_1934_);
lean_dec_ref(v_map_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(lean_object* v_msgData_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_1936_, v___y_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___boxed(lean_object* v_msgData_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(v_msgData_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(lean_object* v_00_u03b1_1946_, lean_object* v_preNode_1947_, lean_object* v_postNode_1948_, lean_object* v___x_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_1947_, v_postNode_1948_, v___x_1949_, v_x_1950_, v_x_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___boxed(lean_object* v_00_u03b1_1956_, lean_object* v_preNode_1957_, lean_object* v_postNode_1958_, lean_object* v___x_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(v_00_u03b1_1956_, v_preNode_1957_, v_postNode_1958_, v___x_1959_, v_x_1960_, v_x_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b2_1966_, lean_object* v_keys_1967_, lean_object* v_vals_1968_, lean_object* v_heq_1969_, lean_object* v_i_1970_, lean_object* v_k_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_1967_, v_vals_1968_, v_i_1970_, v_k_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b2_1973_, lean_object* v_keys_1974_, lean_object* v_vals_1975_, lean_object* v_heq_1976_, lean_object* v_i_1977_, lean_object* v_k_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(v_00_u03b2_1973_, v_keys_1974_, v_vals_1975_, v_heq_1976_, v_i_1977_, v_k_1978_);
lean_dec(v_k_1978_);
lean_dec_ref(v_vals_1975_);
lean_dec_ref(v_keys_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18(lean_object* v_00_u03b2_1980_, lean_object* v_n_1981_, lean_object* v_k_1982_, lean_object* v_v_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v_n_1981_, v_k_1982_, v_v_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(lean_object* v_00_u03b2_1985_, size_t v_depth_1986_, lean_object* v_keys_1987_, lean_object* v_vals_1988_, lean_object* v_heq_1989_, lean_object* v_i_1990_, lean_object* v_entries_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_1986_, v_keys_1987_, v_vals_1988_, v_i_1990_, v_entries_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___boxed(lean_object* v_00_u03b2_1993_, lean_object* v_depth_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_heq_1997_, lean_object* v_i_1998_, lean_object* v_entries_1999_){
_start:
{
size_t v_depth_boxed_2000_; lean_object* v_res_2001_; 
v_depth_boxed_2000_ = lean_unbox_usize(v_depth_1994_);
lean_dec(v_depth_1994_);
v_res_2001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(v_00_u03b2_1993_, v_depth_boxed_2000_, v_keys_1995_, v_vals_1996_, v_heq_1997_, v_i_1998_, v_entries_1999_);
lean_dec_ref(v_vals_1996_);
lean_dec_ref(v_keys_1995_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22(lean_object* v_00_u03c3_2002_, lean_object* v_00_u03c3_2003_, lean_object* v_00_u03b1_2004_, lean_object* v_00_u03b2_2005_, lean_object* v_f_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_2006_, v_x_2007_, v_x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(lean_object* v_00_u03c3_2010_, lean_object* v_00_u03b1_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_f_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_2013_, v_x_2014_, v_x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___boxed(lean_object* v_00_u03c3_2017_, lean_object* v_00_u03b1_2018_, lean_object* v_00_u03b2_2019_, lean_object* v_f_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(v_00_u03c3_2017_, v_00_u03b1_2018_, v_00_u03b2_2019_, v_f_2020_, v_x_2021_, v_x_2022_);
lean_dec_ref(v_x_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_x_2025_, v_x_2026_, v_x_2027_, v_x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(lean_object* v_00_u03b1_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_00_u03c3_2032_, lean_object* v_00_u03c3_2033_, lean_object* v_f_2034_, lean_object* v_as_2035_, size_t v_i_2036_, size_t v_stop_2037_, lean_object* v_b_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_2034_, v_as_2035_, v_i_2036_, v_stop_2037_, v_b_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_00_u03b2_2041_, lean_object* v_00_u03c3_2042_, lean_object* v_00_u03c3_2043_, lean_object* v_f_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_, lean_object* v_b_2048_){
_start:
{
size_t v_i_boxed_2049_; size_t v_stop_boxed_2050_; lean_object* v_res_2051_; 
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2050_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(v_00_u03b1_2040_, v_00_u03b2_2041_, v_00_u03c3_2042_, v_00_u03c3_2043_, v_f_2044_, v_as_2045_, v_i_boxed_2049_, v_stop_boxed_2050_, v_b_2048_);
lean_dec_ref(v_as_2045_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(lean_object* v_00_u03c3_2052_, lean_object* v_00_u03c3_2053_, lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_f_2056_, lean_object* v_keys_2057_, lean_object* v_vals_2058_, lean_object* v_heq_2059_, lean_object* v_i_2060_, lean_object* v_acc_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_2056_, v_keys_2057_, v_vals_2058_, v_i_2060_, v_acc_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___boxed(lean_object* v_00_u03c3_2063_, lean_object* v_00_u03c3_2064_, lean_object* v_00_u03b1_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_f_2067_, lean_object* v_keys_2068_, lean_object* v_vals_2069_, lean_object* v_heq_2070_, lean_object* v_i_2071_, lean_object* v_acc_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(v_00_u03c3_2063_, v_00_u03c3_2064_, v_00_u03b1_2065_, v_00_u03b2_2066_, v_f_2067_, v_keys_2068_, v_vals_2069_, v_heq_2070_, v_i_2071_, v_acc_2072_);
lean_dec_ref(v_vals_2069_);
lean_dec_ref(v_keys_2068_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(lean_object* v_00_u03b1_2074_, lean_object* v_00_u03b2_2075_, lean_object* v_00_u03c3_2076_, lean_object* v_f_2077_, lean_object* v_as_2078_, size_t v_i_2079_, size_t v_stop_2080_, lean_object* v_b_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_2077_, v_as_2078_, v_i_2079_, v_stop_2080_, v_b_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___boxed(lean_object* v_00_u03b1_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_00_u03c3_2085_, lean_object* v_f_2086_, lean_object* v_as_2087_, lean_object* v_i_2088_, lean_object* v_stop_2089_, lean_object* v_b_2090_){
_start:
{
size_t v_i_boxed_2091_; size_t v_stop_boxed_2092_; lean_object* v_res_2093_; 
v_i_boxed_2091_ = lean_unbox_usize(v_i_2088_);
lean_dec(v_i_2088_);
v_stop_boxed_2092_ = lean_unbox_usize(v_stop_2089_);
lean_dec(v_stop_2089_);
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(v_00_u03b1_2083_, v_00_u03b2_2084_, v_00_u03c3_2085_, v_f_2086_, v_as_2087_, v_i_boxed_2091_, v_stop_boxed_2092_, v_b_2090_);
lean_dec_ref(v_as_2087_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(lean_object* v_00_u03c3_2094_, lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_f_2097_, lean_object* v_keys_2098_, lean_object* v_vals_2099_, lean_object* v_heq_2100_, lean_object* v_i_2101_, lean_object* v_acc_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_2097_, v_keys_2098_, v_vals_2099_, v_i_2101_, v_acc_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2104_, lean_object* v_00_u03b1_2105_, lean_object* v_00_u03b2_2106_, lean_object* v_f_2107_, lean_object* v_keys_2108_, lean_object* v_vals_2109_, lean_object* v_heq_2110_, lean_object* v_i_2111_, lean_object* v_acc_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(v_00_u03c3_2104_, v_00_u03b1_2105_, v_00_u03b2_2106_, v_f_2107_, v_keys_2108_, v_vals_2109_, v_heq_2110_, v_i_2111_, v_acc_2112_);
lean_dec_ref(v_vals_2109_);
lean_dec_ref(v_keys_2108_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances));
v___x_2116_ = l_Lean_Elab_Command_addLinter(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
return v_res_2118_;
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
