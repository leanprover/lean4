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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticCheckInstances"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(62, 15, 63, 147, 29, 186, 208, 53)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "enable the linter that type-checks every tactic goal at `.instances` transparency"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "TacticTypeCheck"};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(49, 102, 193, 192, 84, 254, 215, 146)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(116, 222, 67, 228, 15, 224, 52, 25)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(117, 55, 50, 200, 193, 197, 82, 26)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 246, 95, 93, 100, 71, 27, 119)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 8, 58, 244, 180, 197, 6, 42)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__16_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(18, 81, 58, 124, 13, 242, 246, 48)}};
static const lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4____boxed(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2;
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = " tactic goal is not type-correct at `.instances` transparency; "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = " some of the following as `@[implicit_reducible]`:"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "consider using propositional rewriting or marking"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__5_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "consider rephrasing the goal or marking"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__8_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13;
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
static const lean_ctor_object l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__15_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(167, 120, 193, 102, 53, 18, 184, 230)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn___closed__17_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_));
v___x_80_ = l_Lean_Option_register___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4__spec__0(v___x_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4____boxed(lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
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
lean_dec_ref(v___x_131_);
if (lean_obj_tag(v_val_133_) == 1)
{
uint8_t v_v_134_; 
v_v_134_ = lean_ctor_get_uint8(v_val_133_, 0);
lean_dec_ref(v_val_133_);
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
lean_dec_ref(v___x_145_);
if (lean_obj_tag(v_val_146_) == 3)
{
lean_object* v_v_147_; 
v_v_147_ = lean_ctor_get(v_val_146_, 0);
lean_inc(v_v_147_);
lean_dec_ref(v_val_146_);
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
uint8_t v_a_28665__boxed_236_; lean_object* v_res_237_; 
v_a_28665__boxed_236_ = lean_unbox(v_a_229_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1(v_a_28665__boxed_236_, v_x_230_, v_x_231_, v_x_232_, v___y_233_, v___y_234_);
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
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_25683__overap_290_; lean_object* v___x_291_; 
v___x_288_ = lean_box(0);
v___x_289_ = l_instInhabitedOfMonad___redArg(v___x_287_, v___x_288_);
v___x_25683__overap_290_ = lean_panic_fn_borrowed(v___x_289_, v_msg_259_);
lean_dec(v___x_289_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
v___x_291_ = lean_apply_3(v___x_25683__overap_290_, v___y_260_, v___y_261_, lean_box(0));
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
lean_dec_ref(v_x_315_);
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
lean_dec_ref(v_x_315_);
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
lean_dec_ref(v_x_315_);
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
lean_dec_ref(v___x_328_);
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
lean_dec_ref(v___x_360_);
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
lean_dec_ref(v_x_314_);
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
lean_dec_ref(v___x_420_);
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
uint8_t v___y_29107__boxed_497_; uint8_t v_suppressElabErrors_boxed_498_; uint8_t v_res_499_; lean_object* v_r_500_; 
v___y_29107__boxed_497_ = lean_unbox(v___y_494_);
v_suppressElabErrors_boxed_498_ = lean_unbox(v_suppressElabErrors_495_);
v_res_499_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20___lam__0(v___y_29107__boxed_497_, v_suppressElabErrors_boxed_498_, v_x_496_);
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
lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; uint8_t v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; uint8_t v___y_612_; uint8_t v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; lean_object* v___y_616_; uint8_t v___y_640_; uint8_t v___y_641_; lean_object* v___y_642_; uint8_t v___y_643_; lean_object* v___y_644_; uint8_t v___y_648_; uint8_t v___y_649_; uint8_t v___y_650_; uint8_t v___x_665_; uint8_t v___y_667_; uint8_t v___y_668_; uint8_t v___y_669_; uint8_t v___y_671_; uint8_t v___x_683_; 
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
lean_dec_ref(v___x_556_);
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
lean_object* v___x_563_; lean_object* v_currNamespace_564_; lean_object* v_openDecls_565_; lean_object* v_env_566_; lean_object* v_messages_567_; lean_object* v_scopes_568_; lean_object* v_usedQuotCtxts_569_; lean_object* v_nextMacroScope_570_; lean_object* v_maxRecDepth_571_; lean_object* v_ngen_572_; lean_object* v_auxDeclNGen_573_; lean_object* v_infoState_574_; lean_object* v_traceState_575_; lean_object* v_snapshotTasks_576_; lean_object* v_newDecls_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_593_; 
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
v_newDecls_577_ = lean_ctor_get(v___x_563_, 11);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_593_ == 0)
{
v___x_579_ = v___x_563_;
v_isShared_580_ = v_isSharedCheck_593_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_newDecls_577_);
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
lean_ctor_set(v___x_582_, 1, v___y_552_);
lean_inc_ref(v___y_548_);
lean_inc_ref(v___y_551_);
v___x_583_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_583_, 0, v___y_551_);
lean_ctor_set(v___x_583_, 1, v___y_549_);
lean_ctor_set(v___x_583_, 2, v___y_554_);
lean_ctor_set(v___x_583_, 3, v___y_548_);
lean_ctor_set(v___x_583_, 4, v___x_582_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5, v___y_550_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*5 + 1, v___y_553_);
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
lean_ctor_set(v_reuseFailAlloc_592_, 11, v_newDecls_577_);
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
lean_dec(v___y_554_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_549_);
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
lean_dec(v___y_554_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_549_);
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
v___y_549_ = v___x_626_;
v___y_550_ = v___y_613_;
v___y_551_ = v_fileName_617_;
v___y_552_ = v_a_622_;
v___y_553_ = v___y_615_;
v___y_554_ = v___x_628_;
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
lean_dec_ref(v___x_628_);
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
v___y_549_ = v___x_626_;
v___y_550_ = v___y_613_;
v___y_551_ = v_fileName_617_;
v___y_552_ = v_a_622_;
v___y_553_ = v___y_615_;
v___y_554_ = v___x_628_;
v___y_555_ = v___y_545_;
goto v___jp_547_;
}
}
}
}
v___jp_639_:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Syntax_getTailPos_x3f(v___y_642_, v___y_641_);
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
lean_dec_ref(v___x_645_);
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
lean_dec_ref(v___x_651_);
v_ref_653_ = l_Lean_replaceRef(v_ref_540_, v_a_652_);
lean_dec(v_a_652_);
v___x_654_ = l_Lean_Syntax_getPos_x3f(v_ref_653_, v___y_649_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___y_640_ = v___y_648_;
v___y_641_ = v___y_649_;
v___y_642_ = v_ref_653_;
v___y_643_ = v___y_650_;
v___y_644_ = v___x_655_;
goto v___jp_639_;
}
else
{
lean_object* v_val_656_; 
v_val_656_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_654_);
v___y_640_ = v___y_648_;
v___y_641_ = v___y_649_;
v___y_642_ = v_ref_653_;
v___y_643_ = v___y_650_;
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
lean_object* v_name_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_736_; 
v_name_721_ = lean_ctor_get(v_linterOption_715_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_linterOption_715_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_linterOption_715_, 1);
lean_dec(v_unused_737_);
v___x_723_ = v_linterOption_715_;
v_isShared_724_ = v_isSharedCheck_736_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_name_721_);
lean_dec(v_linterOption_715_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_736_;
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
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_735_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_disable_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_729_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___closed__3);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v_disable_731_ = l_Lean_MessageData_note(v___x_730_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v_msg_717_);
lean_ctor_set(v___x_732_, 1, v_disable_731_);
v___x_733_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_733_, 0, v_name_721_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15(v_stx_716_, v___x_733_, v___y_718_, v___y_719_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10___boxed(lean_object* v_linterOption_738_, lean_object* v_stx_739_, lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v_linterOption_738_, v_stx_739_, v_msg_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_stx_739_);
return v_res_744_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0(void){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_745_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_box(1);
v___x_749_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg___closed__4);
v___x_750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__1);
v___x_751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_748_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(lean_object* v_val_754_, uint8_t v_a_755_, lean_object* v___x_756_, lean_object* v___f_757_, lean_object* v_ci_758_, lean_object* v_info_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_st_ref_get(v_val_754_);
v___x_765_ = lean_unbox(v___x_764_);
lean_dec(v___x_764_);
if (v___x_765_ == 0)
{
if (lean_obj_tag(v_info_759_) == 0)
{
lean_object* v_toCommandContextInfo_766_; lean_object* v_i_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_842_; 
v_toCommandContextInfo_766_ = lean_ctor_get(v_ci_758_, 0);
lean_inc_ref(v_toCommandContextInfo_766_);
v_i_767_ = lean_ctor_get(v_info_759_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_info_759_);
if (v_isSharedCheck_842_ == 0)
{
v___x_769_ = v_info_759_;
v_isShared_770_ = v_isSharedCheck_842_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_i_767_);
lean_dec(v_info_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_842_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_parentDecl_x3f_771_; lean_object* v_autoImplicits_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_840_; 
v_parentDecl_x3f_771_ = lean_ctor_get(v_ci_758_, 1);
v_autoImplicits_772_ = lean_ctor_get(v_ci_758_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v_ci_758_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_ci_758_, 0);
lean_dec(v_unused_841_);
v___x_774_ = v_ci_758_;
v_isShared_775_ = v_isSharedCheck_840_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_autoImplicits_772_);
lean_inc(v_parentDecl_x3f_771_);
lean_dec(v_ci_758_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_840_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_env_776_; lean_object* v_cmdEnv_x3f_777_; lean_object* v_fileMap_778_; lean_object* v_options_779_; lean_object* v_currNamespace_780_; lean_object* v_openDecls_781_; lean_object* v_ngen_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_838_; 
v_env_776_ = lean_ctor_get(v_toCommandContextInfo_766_, 0);
v_cmdEnv_x3f_777_ = lean_ctor_get(v_toCommandContextInfo_766_, 1);
v_fileMap_778_ = lean_ctor_get(v_toCommandContextInfo_766_, 2);
v_options_779_ = lean_ctor_get(v_toCommandContextInfo_766_, 4);
v_currNamespace_780_ = lean_ctor_get(v_toCommandContextInfo_766_, 5);
v_openDecls_781_ = lean_ctor_get(v_toCommandContextInfo_766_, 6);
v_ngen_782_ = lean_ctor_get(v_toCommandContextInfo_766_, 7);
v_isSharedCheck_838_ = !lean_is_exclusive(v_toCommandContextInfo_766_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_toCommandContextInfo_766_, 3);
lean_dec(v_unused_839_);
v___x_784_ = v_toCommandContextInfo_766_;
v_isShared_785_ = v_isSharedCheck_838_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_ngen_782_);
lean_inc(v_openDecls_781_);
lean_inc(v_currNamespace_780_);
lean_inc(v_options_779_);
lean_inc(v_fileMap_778_);
lean_inc(v_cmdEnv_x3f_777_);
lean_inc(v_env_776_);
lean_dec(v_toCommandContextInfo_766_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_838_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_toElabInfo_786_; lean_object* v_mctxBefore_787_; lean_object* v_goalsBefore_788_; lean_object* v_mctxAfter_789_; lean_object* v_goalsAfter_790_; lean_object* v___y_792_; lean_object* v___x_823_; 
v_toElabInfo_786_ = lean_ctor_get(v_i_767_, 0);
lean_inc_ref(v_toElabInfo_786_);
v_mctxBefore_787_ = lean_ctor_get(v_i_767_, 1);
lean_inc_ref(v_mctxBefore_787_);
v_goalsBefore_788_ = lean_ctor_get(v_i_767_, 2);
lean_inc(v_goalsBefore_788_);
v_mctxAfter_789_ = lean_ctor_get(v_i_767_, 3);
lean_inc_ref(v_mctxAfter_789_);
v_goalsAfter_790_ = lean_ctor_get(v_i_767_, 4);
lean_inc(v_goalsAfter_790_);
lean_dec_ref(v_i_767_);
lean_inc_ref(v_ngen_782_);
lean_inc(v_openDecls_781_);
lean_inc(v_currNamespace_780_);
lean_inc_ref(v_options_779_);
lean_inc_ref(v_fileMap_778_);
lean_inc(v_cmdEnv_x3f_777_);
lean_inc_ref(v_env_776_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 3, v_mctxBefore_787_);
v___x_823_ = v___x_784_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_env_776_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_cmdEnv_x3f_777_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_fileMap_778_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_mctxBefore_787_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_options_779_);
lean_ctor_set(v_reuseFailAlloc_837_, 5, v_currNamespace_780_);
lean_ctor_set(v_reuseFailAlloc_837_, 6, v_openDecls_781_);
lean_ctor_set(v_reuseFailAlloc_837_, 7, v_ngen_782_);
v___x_823_ = v_reuseFailAlloc_837_;
goto v_reusejp_822_;
}
v___jp_791_:
{
if (lean_obj_tag(v___y_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_806_; 
lean_del_object(v___x_769_);
v_a_793_ = lean_ctor_get(v___y_792_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___y_792_);
if (v_isSharedCheck_806_ == 0)
{
v___x_795_ = v___y_792_;
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___y_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
if (lean_obj_tag(v_a_793_) == 1)
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_stx_800_; lean_object* v___x_801_; 
lean_del_object(v___x_795_);
v_val_797_ = lean_ctor_get(v_a_793_, 0);
lean_inc(v_val_797_);
lean_dec_ref(v_a_793_);
v___x_798_ = lean_box(v_a_755_);
v___x_799_ = lean_st_ref_set(v_val_754_, v___x_798_);
v_stx_800_ = lean_ctor_get(v_toElabInfo_786_, 1);
lean_inc(v_stx_800_);
lean_dec_ref(v_toElabInfo_786_);
v___x_801_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10(v___x_756_, v_stx_800_, v_val_797_, v___y_761_, v___y_762_);
lean_dec(v_stx_800_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_a_793_);
lean_dec_ref(v_toElabInfo_786_);
lean_dec_ref(v___x_756_);
v___x_802_ = lean_box(0);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_802_);
v___x_804_ = v___x_795_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_toElabInfo_786_);
lean_dec_ref(v___x_756_);
v_a_807_ = lean_ctor_get(v___y_792_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___y_792_);
if (v_isSharedCheck_821_ == 0)
{
v___x_809_ = v___y_792_;
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___y_792_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_821_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_ref_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v_ref_811_ = lean_ctor_get(v___y_761_, 7);
v___x_812_ = lean_io_error_to_string(v_a_807_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 3);
lean_ctor_set(v___x_769_, 0, v___x_812_);
v___x_814_ = v___x_769_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_820_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = l_Lean_MessageData_ofFormat(v___x_814_);
lean_inc(v_ref_811_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_ref_811_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
lean_inc_ref(v_autoImplicits_772_);
lean_inc(v_parentDecl_x3f_771_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_823_);
v___x_825_ = v___x_774_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_parentDecl_x3f_771_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_autoImplicits_772_);
v___x_825_ = v_reuseFailAlloc_836_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__2);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3));
lean_inc_ref(v___f_757_);
v___x_828_ = lean_apply_2(v___f_757_, v___x_827_, v_goalsBefore_788_);
v___x_829_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_825_, v___x_826_, v___x_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
if (lean_obj_tag(v_a_830_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_831_, 0, v_env_776_);
lean_ctor_set(v___x_831_, 1, v_cmdEnv_x3f_777_);
lean_ctor_set(v___x_831_, 2, v_fileMap_778_);
lean_ctor_set(v___x_831_, 3, v_mctxAfter_789_);
lean_ctor_set(v___x_831_, 4, v_options_779_);
lean_ctor_set(v___x_831_, 5, v_currNamespace_780_);
lean_ctor_set(v___x_831_, 6, v_openDecls_781_);
lean_ctor_set(v___x_831_, 7, v_ngen_782_);
v___x_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_parentDecl_x3f_771_);
lean_ctor_set(v___x_832_, 2, v_autoImplicits_772_);
v___x_833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__4));
v___x_834_ = lean_apply_2(v___f_757_, v___x_833_, v_goalsAfter_790_);
v___x_835_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v___x_832_, v___x_826_, v___x_834_);
v___y_792_ = v___x_835_;
goto v___jp_791_;
}
else
{
lean_dec_ref(v_a_830_);
lean_dec(v_goalsAfter_790_);
lean_dec_ref(v_mctxAfter_789_);
lean_dec_ref(v_ngen_782_);
lean_dec(v_openDecls_781_);
lean_dec(v_currNamespace_780_);
lean_dec_ref(v_options_779_);
lean_dec_ref(v_fileMap_778_);
lean_dec(v_cmdEnv_x3f_777_);
lean_dec_ref(v_env_776_);
lean_dec_ref(v_autoImplicits_772_);
lean_dec(v_parentDecl_x3f_771_);
lean_dec_ref(v___f_757_);
v___y_792_ = v___x_829_;
goto v___jp_791_;
}
}
else
{
lean_dec(v_goalsAfter_790_);
lean_dec_ref(v_mctxAfter_789_);
lean_dec_ref(v_ngen_782_);
lean_dec(v_openDecls_781_);
lean_dec(v_currNamespace_780_);
lean_dec_ref(v_options_779_);
lean_dec_ref(v_fileMap_778_);
lean_dec(v_cmdEnv_x3f_777_);
lean_dec_ref(v_env_776_);
lean_dec_ref(v_autoImplicits_772_);
lean_dec(v_parentDecl_x3f_771_);
lean_dec_ref(v___f_757_);
v___y_792_ = v___x_829_;
goto v___jp_791_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec_ref(v_info_759_);
lean_dec_ref(v_ci_758_);
lean_dec_ref(v___f_757_);
lean_dec_ref(v___x_756_);
v___x_843_ = lean_box(0);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_info_759_);
lean_dec_ref(v_ci_758_);
lean_dec_ref(v___f_757_);
lean_dec_ref(v___x_756_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed(lean_object* v_val_847_, lean_object* v_a_848_, lean_object* v___x_849_, lean_object* v___f_850_, lean_object* v_ci_851_, lean_object* v_info_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v_a_29575__boxed_857_; lean_object* v_res_858_; 
v_a_29575__boxed_857_ = lean_unbox(v_a_848_);
v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2(v_val_847_, v_a_29575__boxed_857_, v___x_849_, v___f_850_, v_ci_851_, v_info_852_, v_x_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_x_853_);
lean_dec(v_val_847_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(lean_object* v___x_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v___x_859_);
v___x_862_ = lean_array_to_list(v_a_861_);
return v___x_862_;
}
else
{
lean_object* v_head_863_; lean_object* v_tail_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_head_863_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_head_863_);
v_tail_864_ = lean_ctor_get(v_a_860_, 1);
lean_inc(v_tail_864_);
lean_dec_ref(v_a_860_);
v_fst_865_ = lean_ctor_get(v_head_863_, 0);
lean_inc(v_fst_865_);
v_snd_866_ = lean_ctor_get(v_head_863_, 1);
lean_inc(v_snd_866_);
lean_dec(v_head_863_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_nat_dec_lt(v___x_867_, v_snd_866_);
lean_dec(v_snd_866_);
if (v___x_868_ == 0)
{
lean_dec(v_fst_865_);
v_a_860_ = v_tail_864_;
goto _start;
}
else
{
uint8_t v___x_870_; 
lean_inc(v_fst_865_);
lean_inc_ref(v___x_859_);
v___x_870_ = lean_get_reducibility_status(v___x_859_, v_fst_865_);
if (v___x_870_ == 1)
{
uint8_t v___x_871_; 
lean_inc_ref(v___x_859_);
v___x_871_ = l_Lean_Meta_isInstanceCore(v___x_859_, v_fst_865_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = l_Lean_MessageData_ofConstName(v_fst_865_, v___x_871_);
v___x_873_ = lean_array_push(v_a_861_, v___x_872_);
v_a_860_ = v_tail_864_;
v_a_861_ = v___x_873_;
goto _start;
}
else
{
lean_dec(v_fst_865_);
v_a_860_ = v_tail_864_;
goto _start;
}
}
else
{
lean_dec(v_fst_865_);
v_a_860_ = v_tail_864_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(lean_object* v_o_879_, lean_object* v_k_880_, uint8_t v_v_881_){
_start:
{
lean_object* v_map_882_; uint8_t v_hasTrace_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_897_; 
v_map_882_ = lean_ctor_get(v_o_879_, 0);
v_hasTrace_883_ = lean_ctor_get_uint8(v_o_879_, sizeof(void*)*1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_o_879_);
if (v_isSharedCheck_897_ == 0)
{
v___x_885_ = v_o_879_;
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_map_882_);
lean_dec(v_o_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_887_, 0, v_v_881_);
lean_inc(v_k_880_);
v___x_888_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_880_, v___x_887_, v_map_882_);
if (v_hasTrace_883_ == 0)
{
lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_892_; 
v___x_889_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___closed__0));
v___x_890_ = l_Lean_Name_isPrefixOf(v___x_889_, v_k_880_);
lean_dec(v_k_880_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_888_);
v___x_892_ = v___x_885_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_888_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*1, v___x_890_);
return v___x_892_;
}
}
else
{
lean_object* v___x_895_; 
lean_dec(v_k_880_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_888_);
v___x_895_ = v___x_885_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_896_, sizeof(void*)*1, v_hasTrace_883_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2___boxed(lean_object* v_o_898_, lean_object* v_k_899_, lean_object* v_v_900_){
_start:
{
uint8_t v_v_boxed_901_; lean_object* v_res_902_; 
v_v_boxed_901_ = lean_unbox(v_v_900_);
v_res_902_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_o_898_, v_k_899_, v_v_boxed_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(lean_object* v_opts_903_, lean_object* v_opt_904_, uint8_t v_val_905_){
_start:
{
lean_object* v_name_906_; lean_object* v___x_907_; 
v_name_906_ = lean_ctor_get(v_opt_904_, 0);
lean_inc(v_name_906_);
lean_dec_ref(v_opt_904_);
v___x_907_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2_spec__2(v_opts_903_, v_name_906_, v_val_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2___boxed(lean_object* v_opts_908_, lean_object* v_opt_909_, lean_object* v_val_910_){
_start:
{
uint8_t v_val_boxed_911_; lean_object* v_res_912_; 
v_val_boxed_911_ = lean_unbox(v_val_910_);
v_res_912_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_opts_908_, v_opt_909_, v_val_boxed_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(lean_object* v_f_913_, lean_object* v_keys_914_, lean_object* v_vals_915_, lean_object* v_i_916_, lean_object* v_acc_917_){
_start:
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_array_get_size(v_keys_914_);
v___x_919_ = lean_nat_dec_lt(v_i_916_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec(v_i_916_);
lean_dec_ref(v_f_913_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v_acc_917_);
return v___x_920_;
}
else
{
lean_object* v_k_921_; lean_object* v_v_922_; lean_object* v___x_923_; 
v_k_921_ = lean_array_fget_borrowed(v_keys_914_, v_i_916_);
v_v_922_ = lean_array_fget_borrowed(v_vals_915_, v_i_916_);
lean_inc_ref(v_f_913_);
lean_inc(v_v_922_);
lean_inc(v_k_921_);
v___x_923_ = lean_apply_3(v_f_913_, v_acc_917_, v_k_921_, v_v_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_dec(v_i_916_);
lean_dec_ref(v_f_913_);
return v___x_923_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_i_916_, v___x_925_);
lean_dec(v_i_916_);
v_i_916_ = v___x_926_;
v_acc_917_ = v_a_924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg___boxed(lean_object* v_f_928_, lean_object* v_keys_929_, lean_object* v_vals_930_, lean_object* v_i_931_, lean_object* v_acc_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_928_, v_keys_929_, v_vals_930_, v_i_931_, v_acc_932_);
lean_dec_ref(v_vals_930_);
lean_dec_ref(v_keys_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(lean_object* v_f_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
lean_object* v_es_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_957_; 
v_es_937_ = lean_ctor_get(v_x_935_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_x_935_);
if (v_isSharedCheck_957_ == 0)
{
v___x_939_ = v_x_935_;
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_es_937_);
lean_dec(v_x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_array_get_size(v_es_937_);
v___x_943_ = lean_nat_dec_lt(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v_es_937_);
lean_dec_ref(v_f_934_);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
lean_ctor_set(v___x_939_, 0, v_x_936_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_x_936_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
uint8_t v___x_947_; 
v___x_947_ = lean_nat_dec_le(v___x_942_, v___x_942_);
if (v___x_947_ == 0)
{
if (v___x_943_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v_es_937_);
lean_dec_ref(v_f_934_);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
lean_ctor_set(v___x_939_, 0, v_x_936_);
v___x_949_ = v___x_939_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_x_936_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
lean_del_object(v___x_939_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_942_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_934_, v_es_937_, v___x_951_, v___x_952_, v_x_936_);
lean_dec_ref(v_es_937_);
return v___x_953_;
}
}
else
{
size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
lean_del_object(v___x_939_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = lean_usize_of_nat(v___x_942_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_934_, v_es_937_, v___x_954_, v___x_955_, v_x_936_);
lean_dec_ref(v_es_937_);
return v___x_956_;
}
}
}
}
else
{
lean_object* v_ks_958_; lean_object* v_vs_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_ks_958_ = lean_ctor_get(v_x_935_, 0);
lean_inc_ref(v_ks_958_);
v_vs_959_ = lean_ctor_get(v_x_935_, 1);
lean_inc_ref(v_vs_959_);
lean_dec_ref(v_x_935_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_934_, v_ks_958_, v_vs_959_, v___x_960_, v_x_936_);
lean_dec_ref(v_vs_959_);
lean_dec_ref(v_ks_958_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(lean_object* v_f_962_, lean_object* v_as_963_, size_t v_i_964_, size_t v_stop_965_, lean_object* v_b_966_){
_start:
{
lean_object* v_a_968_; lean_object* v___y_973_; uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_eq(v_i_964_, v_stop_965_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_array_uget_borrowed(v_as_963_, v_i_964_);
switch(lean_obj_tag(v___x_976_))
{
case 0:
{
lean_object* v_key_977_; lean_object* v_val_978_; lean_object* v___x_979_; 
v_key_977_ = lean_ctor_get(v___x_976_, 0);
v_val_978_ = lean_ctor_get(v___x_976_, 1);
lean_inc_ref(v_f_962_);
lean_inc(v_val_978_);
lean_inc(v_key_977_);
v___x_979_ = lean_apply_3(v_f_962_, v_b_966_, v_key_977_, v_val_978_);
v___y_973_ = v___x_979_;
goto v___jp_972_;
}
case 1:
{
lean_object* v_node_980_; lean_object* v___x_981_; 
v_node_980_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_node_980_);
lean_inc_ref(v_f_962_);
v___x_981_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_962_, v_node_980_, v_b_966_);
v___y_973_ = v___x_981_;
goto v___jp_972_;
}
default: 
{
v_a_968_ = v_b_966_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v___x_982_; 
lean_dec_ref(v_f_962_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_b_966_);
return v___x_982_;
}
v___jp_967_:
{
size_t v___x_969_; size_t v___x_970_; 
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_964_, v___x_969_);
v_i_964_ = v___x_970_;
v_b_966_ = v_a_968_;
goto _start;
}
v___jp_972_:
{
if (lean_obj_tag(v___y_973_) == 0)
{
lean_dec_ref(v_f_962_);
return v___y_973_;
}
else
{
lean_object* v_a_974_; 
v_a_974_ = lean_ctor_get(v___y_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___y_973_);
v_a_968_ = v_a_974_;
goto v___jp_967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg___boxed(lean_object* v_f_983_, lean_object* v_as_984_, lean_object* v_i_985_, lean_object* v_stop_986_, lean_object* v_b_987_){
_start:
{
size_t v_i_boxed_988_; size_t v_stop_boxed_989_; lean_object* v_res_990_; 
v_i_boxed_988_ = lean_unbox_usize(v_i_985_);
lean_dec(v_i_985_);
v_stop_boxed_989_ = lean_unbox_usize(v_stop_986_);
lean_dec(v_stop_986_);
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_983_, v_as_984_, v_i_boxed_988_, v_stop_boxed_989_, v_b_987_);
lean_dec_ref(v_as_984_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0(lean_object* v_f_991_, lean_object* v_s_992_, lean_object* v_a_993_, lean_object* v_b_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_a_993_);
lean_ctor_set(v___x_995_, 1, v_b_994_);
v___x_996_ = lean_apply_2(v_f_991_, v___x_995_, v_s_992_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_996_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_996_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(lean_object* v_map_1013_, lean_object* v_init_1014_, lean_object* v_f_1015_){
_start:
{
lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v_a_1018_; 
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1016_, 0, v_f_1015_);
lean_inc_ref(v_map_1013_);
v___x_1017_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v___f_1016_, v_map_1013_, v_init_1014_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
return v_a_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg___boxed(lean_object* v_map_1019_, lean_object* v_init_1020_, lean_object* v_f_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_1019_, v_init_1020_, v_f_1021_);
lean_dec_ref(v_map_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_ks_1027_; lean_object* v_vs_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1052_; 
v_ks_1027_ = lean_ctor_get(v_x_1023_, 0);
v_vs_1028_ = lean_ctor_get(v_x_1023_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1023_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1030_ = v_x_1023_;
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_vs_1028_);
lean_inc(v_ks_1027_);
lean_dec(v_x_1023_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_array_get_size(v_ks_1027_);
v___x_1033_ = lean_nat_dec_lt(v_x_1024_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_dec(v_x_1024_);
v___x_1034_ = lean_array_push(v_ks_1027_, v_x_1025_);
v___x_1035_ = lean_array_push(v_vs_1028_, v_x_1026_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1035_);
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1037_ = v___x_1030_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v_k_x27_1039_; uint8_t v___x_1040_; 
v_k_x27_1039_ = lean_array_fget_borrowed(v_ks_1027_, v_x_1024_);
v___x_1040_ = lean_name_eq(v_x_1025_, v_k_x27_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1042_; 
if (v_isShared_1031_ == 0)
{
v___x_1042_ = v___x_1030_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_ks_1027_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_vs_1028_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_x_1024_, v___x_1043_);
lean_dec(v_x_1024_);
v_x_1023_ = v___x_1042_;
v_x_1024_ = v___x_1044_;
goto _start;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = lean_array_fset(v_ks_1027_, v_x_1024_, v_x_1025_);
v___x_1048_ = lean_array_fset(v_vs_1028_, v_x_1024_, v_x_1026_);
lean_dec(v_x_1024_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1048_);
lean_ctor_set(v___x_1030_, 0, v___x_1047_);
v___x_1050_ = v___x_1030_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(lean_object* v_n_1053_, lean_object* v_k_1054_, lean_object* v_v_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_n_1053_, v___x_1056_, v_k_1054_, v_v_1055_);
return v___x_1057_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1058_; uint64_t v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(1723u);
v___x_1059_ = lean_uint64_of_nat(v___x_1058_);
return v___x_1059_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0(void){
_start:
{
size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; 
v___x_1060_ = ((size_t)5ULL);
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_shift_left(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; 
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__0);
v___x_1065_ = lean_usize_sub(v___x_1064_, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2(void){
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
lean_object* v_es_1072_; size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; lean_object* v_j_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_es_1072_ = lean_ctor_get(v_x_1067_, 0);
v___x_1073_ = ((size_t)5ULL);
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1);
v___x_1076_ = lean_usize_land(v_x_1068_, v___x_1075_);
v_j_1077_ = lean_usize_to_nat(v___x_1076_);
v___x_1078_ = lean_array_get_size(v_es_1072_);
v___x_1079_ = lean_nat_dec_lt(v_j_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec(v_j_1077_);
lean_dec(v_x_1071_);
lean_dec(v_x_1070_);
return v_x_1067_;
}
else
{
lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1116_; 
lean_inc_ref(v_es_1072_);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v_x_1067_, 0);
lean_dec(v_unused_1117_);
v___x_1081_ = v_x_1067_;
v_isShared_1082_ = v_isSharedCheck_1116_;
goto v_resetjp_1080_;
}
else
{
lean_dec(v_x_1067_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1116_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_v_1083_; lean_object* v___x_1084_; lean_object* v_xs_x27_1085_; lean_object* v___y_1087_; 
v_v_1083_ = lean_array_fget(v_es_1072_, v_j_1077_);
v___x_1084_ = lean_box(0);
v_xs_x27_1085_ = lean_array_fset(v_es_1072_, v_j_1077_, v___x_1084_);
switch(lean_obj_tag(v_v_1083_))
{
case 0:
{
lean_object* v_key_1092_; lean_object* v_val_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1103_; 
v_key_1092_ = lean_ctor_get(v_v_1083_, 0);
v_val_1093_ = lean_ctor_get(v_v_1083_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_v_1083_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1095_ = v_v_1083_;
v_isShared_1096_ = v_isSharedCheck_1103_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_val_1093_);
lean_inc(v_key_1092_);
lean_dec(v_v_1083_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1103_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_name_eq(v_x_1070_, v_key_1092_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_del_object(v___x_1095_);
v___x_1098_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1092_, v_val_1093_, v_x_1070_, v_x_1071_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
v___y_1087_ = v___x_1099_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_val_1093_);
lean_dec(v_key_1092_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_x_1071_);
lean_ctor_set(v___x_1095_, 0, v_x_1070_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_x_1070_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_x_1071_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
v___y_1087_ = v___x_1101_;
goto v___jp_1086_;
}
}
}
}
case 1:
{
lean_object* v_node_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_node_1104_ = lean_ctor_get(v_v_1083_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_v_1083_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v_v_1083_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_node_1104_);
lean_dec(v_v_1083_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1108_ = lean_usize_shift_right(v_x_1068_, v___x_1073_);
v___x_1109_ = lean_usize_add(v_x_1069_, v___x_1074_);
v___x_1110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_node_1104_, v___x_1108_, v___x_1109_, v_x_1070_, v_x_1071_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1112_ = v___x_1106_;
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
v___y_1087_ = v___x_1112_;
goto v___jp_1086_;
}
}
}
default: 
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_x_1070_);
lean_ctor_set(v___x_1115_, 1, v_x_1071_);
v___y_1087_ = v___x_1115_;
goto v___jp_1086_;
}
}
v___jp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_array_fset(v_xs_x27_1085_, v_j_1077_, v___y_1087_);
lean_dec(v_j_1077_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1088_);
v___x_1090_ = v___x_1081_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
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
v___x_1131_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__2);
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
size_t v_x_30056__boxed_1175_; size_t v_x_30057__boxed_1176_; lean_object* v_res_1177_; 
v_x_30056__boxed_1175_ = lean_unbox_usize(v_x_1171_);
lean_dec(v_x_1171_);
v_x_30057__boxed_1176_ = lean_unbox_usize(v_x_1172_);
lean_dec(v_x_1172_);
v_res_1177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1170_, v_x_30056__boxed_1175_, v_x_30057__boxed_1176_, v_x_1173_, v_x_1174_);
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
lean_object* v_es_1210_; lean_object* v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_j_1215_; lean_object* v___x_1216_; 
v_es_1210_ = lean_ctor_get(v_x_1207_, 0);
v___x_1211_ = lean_box(2);
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg___closed__1);
v___x_1214_ = lean_usize_land(v_x_1208_, v___x_1213_);
v_j_1215_ = lean_usize_to_nat(v___x_1214_);
v___x_1216_ = lean_array_get_borrowed(v___x_1211_, v_es_1210_, v_j_1215_);
lean_dec(v_j_1215_);
switch(lean_obj_tag(v___x_1216_))
{
case 0:
{
lean_object* v_key_1217_; lean_object* v_val_1218_; uint8_t v___x_1219_; 
v_key_1217_ = lean_ctor_get(v___x_1216_, 0);
v_val_1218_ = lean_ctor_get(v___x_1216_, 1);
v___x_1219_ = lean_name_eq(v_x_1209_, v_key_1217_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_box(0);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; 
lean_inc(v_val_1218_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_val_1218_);
return v___x_1221_;
}
}
case 1:
{
lean_object* v_node_1222_; size_t v___x_1223_; 
v_node_1222_ = lean_ctor_get(v___x_1216_, 0);
v___x_1223_ = lean_usize_shift_right(v_x_1208_, v___x_1212_);
v_x_1207_ = v_node_1222_;
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
size_t v_x_30267__boxed_1233_; lean_object* v_res_1234_; 
v_x_30267__boxed_1233_ = lean_unbox_usize(v_x_1231_);
lean_dec(v_x_1231_);
v_res_1234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1230_, v_x_30267__boxed_1233_, v_x_1232_);
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
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__6));
v___x_1383_ = l_Lean_MessageData_ofFormat(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__9));
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1389_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__11);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__12);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(uint8_t v_a_1394_, lean_object* v_kind_1395_, lean_object* v___x_1396_, lean_object* v_a_1397_, uint8_t v___x_1398_, lean_object* v_diag_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; lean_object* v___x_1448_; lean_object* v_fileName_1449_; lean_object* v_fileMap_1450_; lean_object* v_options_1451_; lean_object* v_currRecDepth_1452_; lean_object* v_ref_1453_; lean_object* v_currNamespace_1454_; lean_object* v_openDecls_1455_; lean_object* v_initHeartbeats_1456_; lean_object* v_maxHeartbeats_1457_; lean_object* v_quotContext_1458_; lean_object* v_currMacroScope_1459_; lean_object* v_cancelTk_x3f_1460_; uint8_t v_suppressElabErrors_1461_; lean_object* v_inheritedTraceOptions_1462_; lean_object* v_env_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; lean_object* v_fileName_1468_; lean_object* v_fileMap_1469_; lean_object* v_currRecDepth_1470_; lean_object* v_ref_1471_; lean_object* v_currNamespace_1472_; lean_object* v_openDecls_1473_; lean_object* v_initHeartbeats_1474_; lean_object* v_maxHeartbeats_1475_; lean_object* v_quotContext_1476_; lean_object* v_currMacroScope_1477_; lean_object* v_cancelTk_x3f_1478_; uint8_t v_suppressElabErrors_1479_; lean_object* v_inheritedTraceOptions_1480_; lean_object* v___y_1481_; uint8_t v___y_1521_; uint8_t v___x_1543_; 
v___x_1448_ = lean_st_ref_get(v___y_1403_);
v_fileName_1449_ = lean_ctor_get(v___y_1402_, 0);
v_fileMap_1450_ = lean_ctor_get(v___y_1402_, 1);
v_options_1451_ = lean_ctor_get(v___y_1402_, 2);
v_currRecDepth_1452_ = lean_ctor_get(v___y_1402_, 3);
v_ref_1453_ = lean_ctor_get(v___y_1402_, 5);
v_currNamespace_1454_ = lean_ctor_get(v___y_1402_, 6);
v_openDecls_1455_ = lean_ctor_get(v___y_1402_, 7);
v_initHeartbeats_1456_ = lean_ctor_get(v___y_1402_, 8);
v_maxHeartbeats_1457_ = lean_ctor_get(v___y_1402_, 9);
v_quotContext_1458_ = lean_ctor_get(v___y_1402_, 10);
v_currMacroScope_1459_ = lean_ctor_get(v___y_1402_, 11);
v_cancelTk_x3f_1460_ = lean_ctor_get(v___y_1402_, 12);
v_suppressElabErrors_1461_ = lean_ctor_get_uint8(v___y_1402_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1462_ = lean_ctor_get(v___y_1402_, 13);
v_env_1463_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_ref(v_env_1463_);
lean_dec(v___x_1448_);
v___x_1464_ = l_Lean_diagnostics;
lean_inc_ref(v_options_1451_);
v___x_1465_ = l_Lean_Option_set___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__2(v_options_1451_, v___x_1464_, v_a_1394_);
v___x_1466_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__3(v___x_1465_, v___x_1464_);
v___x_1543_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1463_);
lean_dec_ref(v_env_1463_);
if (v___x_1543_ == 0)
{
if (v___x_1466_ == 0)
{
v_fileName_1468_ = v_fileName_1449_;
v_fileMap_1469_ = v_fileMap_1450_;
v_currRecDepth_1470_ = v_currRecDepth_1452_;
v_ref_1471_ = v_ref_1453_;
v_currNamespace_1472_ = v_currNamespace_1454_;
v_openDecls_1473_ = v_openDecls_1455_;
v_initHeartbeats_1474_ = v_initHeartbeats_1456_;
v_maxHeartbeats_1475_ = v_maxHeartbeats_1457_;
v_quotContext_1476_ = v_quotContext_1458_;
v_currMacroScope_1477_ = v_currMacroScope_1459_;
v_cancelTk_x3f_1478_ = v_cancelTk_x3f_1460_;
v_suppressElabErrors_1479_ = v_suppressElabErrors_1461_;
v_inheritedTraceOptions_1480_ = v_inheritedTraceOptions_1462_;
v___y_1481_ = v___y_1403_;
goto v___jp_1467_;
}
else
{
v___y_1521_ = v___x_1543_;
goto v___jp_1520_;
}
}
else
{
v___y_1521_ = v___x_1466_;
goto v___jp_1520_;
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
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1414_ = l_Lean_stringToMessageData(v_kind_1395_);
v___x_1415_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__1);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
lean_inc_ref(v___y_1413_);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v___y_1413_);
v___x_1418_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__3);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__4);
v___x_1421_ = l_Lean_MessageData_joinSep(v___y_1412_, v___x_1420_);
v___x_1422_ = l_Lean_indentD(v___x_1421_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1419_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
v___jp_1426_:
{
if (v___y_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_diag_1433_; lean_object* v_unfoldCounter_1434_; lean_object* v_env_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
lean_dec_ref(v___y_1427_);
v___x_1431_ = lean_st_ref_get(v___y_1401_);
v___x_1432_ = lean_st_ref_get(v___y_1429_);
v_diag_1433_ = lean_ctor_get(v___x_1431_, 4);
lean_inc_ref(v_diag_1433_);
lean_dec(v___x_1431_);
v_unfoldCounter_1434_ = lean_ctor_get(v_diag_1433_, 0);
lean_inc_ref(v_unfoldCounter_1434_);
lean_dec_ref(v_diag_1433_);
v_env_1435_ = lean_ctor_get(v___x_1432_, 0);
lean_inc_ref(v_env_1435_);
lean_dec(v___x_1432_);
v___x_1436_ = l_Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5(v___y_1428_, v_unfoldCounter_1434_);
lean_dec_ref(v___y_1428_);
v___x_1437_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v___x_1436_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = lean_mk_empty_array_with_capacity(v___x_1396_);
v___x_1439_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__7(v_env_1435_, v___x_1437_, v___x_1438_);
v___x_1440_ = l_List_isEmpty___redArg(v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___closed__3));
v___x_1442_ = lean_string_dec_eq(v_kind_1395_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__7);
v___y_1412_ = v___x_1439_;
v___y_1413_ = v___x_1443_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__10);
v___y_1412_ = v___x_1439_;
v___y_1413_ = v___x_1444_;
goto v___jp_1411_;
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v___x_1439_);
lean_dec_ref(v_kind_1395_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_kind_1395_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1427_);
return v___x_1447_;
}
}
v___jp_1467_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1482_ = l_Lean_maxRecDepth;
v___x_1483_ = l_Lean_Option_get___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__4(v___x_1465_, v___x_1482_);
lean_inc_ref(v_inheritedTraceOptions_1480_);
lean_inc(v_cancelTk_x3f_1478_);
lean_inc(v_currMacroScope_1477_);
lean_inc(v_quotContext_1476_);
lean_inc(v_maxHeartbeats_1475_);
lean_inc(v_initHeartbeats_1474_);
lean_inc(v_openDecls_1473_);
lean_inc(v_currNamespace_1472_);
lean_inc(v_ref_1471_);
lean_inc(v_currRecDepth_1470_);
lean_inc_ref(v_fileMap_1469_);
lean_inc_ref(v_fileName_1468_);
v___x_1484_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1484_, 0, v_fileName_1468_);
lean_ctor_set(v___x_1484_, 1, v_fileMap_1469_);
lean_ctor_set(v___x_1484_, 2, v___x_1465_);
lean_ctor_set(v___x_1484_, 3, v_currRecDepth_1470_);
lean_ctor_set(v___x_1484_, 4, v___x_1483_);
lean_ctor_set(v___x_1484_, 5, v_ref_1471_);
lean_ctor_set(v___x_1484_, 6, v_currNamespace_1472_);
lean_ctor_set(v___x_1484_, 7, v_openDecls_1473_);
lean_ctor_set(v___x_1484_, 8, v_initHeartbeats_1474_);
lean_ctor_set(v___x_1484_, 9, v_maxHeartbeats_1475_);
lean_ctor_set(v___x_1484_, 10, v_quotContext_1476_);
lean_ctor_set(v___x_1484_, 11, v_currMacroScope_1477_);
lean_ctor_set(v___x_1484_, 12, v_cancelTk_x3f_1478_);
lean_ctor_set(v___x_1484_, 13, v_inheritedTraceOptions_1480_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*14, v___x_1466_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*14 + 1, v_suppressElabErrors_1479_);
lean_inc_ref(v_a_1397_);
v___x_1485_ = l_Lean_Meta_check(v_a_1397_, v___x_1398_, v___y_1400_, v___y_1401_, v___x_1484_, v___y_1481_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v_mctx_1488_; lean_object* v_cache_1489_; lean_object* v_zetaDeltaFVarIds_1490_; lean_object* v_postponed_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v___x_1485_);
v___x_1486_ = lean_st_ref_get(v___y_1401_);
v___x_1487_ = lean_st_ref_take(v___y_1401_);
v_mctx_1488_ = lean_ctor_get(v___x_1487_, 0);
v_cache_1489_ = lean_ctor_get(v___x_1487_, 1);
v_zetaDeltaFVarIds_1490_ = lean_ctor_get(v___x_1487_, 2);
v_postponed_1491_ = lean_ctor_get(v___x_1487_, 3);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v___x_1487_, 4);
lean_dec(v_unused_1516_);
v___x_1493_ = v___x_1487_;
v_isShared_1494_ = v_isSharedCheck_1515_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_postponed_1491_);
lean_inc(v_zetaDeltaFVarIds_1490_);
lean_inc(v_cache_1489_);
lean_inc(v_mctx_1488_);
lean_dec(v___x_1487_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1515_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_diag_1399_);
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_mctx_1488_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_cache_1489_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_zetaDeltaFVarIds_1490_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_postponed_1491_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_diag_1399_);
v___x_1496_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_st_ref_set(v___y_1401_, v___x_1496_);
v___x_1498_ = 3;
v___x_1499_ = l_Lean_Meta_check(v_a_1397_, v___x_1498_, v___y_1400_, v___y_1401_, v___x_1484_, v___y_1481_);
lean_dec_ref(v___x_1484_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v___x_1486_);
lean_dec_ref(v_kind_1395_);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___x_1499_, 0);
lean_dec(v_unused_1508_);
v___x_1501_ = v___x_1499_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v___x_1499_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_box(0);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
lean_object* v_diag_1509_; lean_object* v_a_1510_; lean_object* v_unfoldCounter_1511_; uint8_t v___x_1512_; 
v_diag_1509_ = lean_ctor_get(v___x_1486_, 4);
lean_inc_ref(v_diag_1509_);
lean_dec(v___x_1486_);
v_a_1510_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1499_);
v_unfoldCounter_1511_ = lean_ctor_get(v_diag_1509_, 0);
lean_inc_ref(v_unfoldCounter_1511_);
lean_dec_ref(v_diag_1509_);
v___x_1512_ = l_Lean_Exception_isInterrupt(v_a_1510_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; 
lean_inc(v_a_1510_);
v___x_1513_ = l_Lean_Exception_isRuntime(v_a_1510_);
v___y_1427_ = v_a_1510_;
v___y_1428_ = v_unfoldCounter_1511_;
v___y_1429_ = v___y_1481_;
v___y_1430_ = v___x_1513_;
goto v___jp_1426_;
}
else
{
v___y_1427_ = v_a_1510_;
v___y_1428_ = v_unfoldCounter_1511_;
v___y_1429_ = v___y_1481_;
v___y_1430_ = v___x_1512_;
goto v___jp_1426_;
}
}
}
}
}
else
{
lean_object* v_a_1517_; uint8_t v___x_1518_; 
lean_dec_ref(v___x_1484_);
lean_dec_ref(v_diag_1399_);
lean_dec_ref(v_a_1397_);
lean_dec_ref(v_kind_1395_);
v_a_1517_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1485_);
v___x_1518_ = l_Lean_Exception_isInterrupt(v_a_1517_);
if (v___x_1518_ == 0)
{
uint8_t v___x_1519_; 
lean_inc(v_a_1517_);
v___x_1519_ = l_Lean_Exception_isRuntime(v_a_1517_);
v___y_1406_ = v_a_1517_;
v___y_1407_ = v___x_1519_;
goto v___jp_1405_;
}
else
{
v___y_1406_ = v_a_1517_;
v___y_1407_ = v___x_1518_;
goto v___jp_1405_;
}
}
}
v___jp_1520_:
{
if (v___y_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v_env_1523_; lean_object* v_nextMacroScope_1524_; lean_object* v_ngen_1525_; lean_object* v_auxDeclNGen_1526_; lean_object* v_traceState_1527_; lean_object* v_messages_1528_; lean_object* v_infoState_1529_; lean_object* v_snapshotTasks_1530_; lean_object* v_newDecls_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1541_; 
v___x_1522_ = lean_st_ref_take(v___y_1403_);
v_env_1523_ = lean_ctor_get(v___x_1522_, 0);
v_nextMacroScope_1524_ = lean_ctor_get(v___x_1522_, 1);
v_ngen_1525_ = lean_ctor_get(v___x_1522_, 2);
v_auxDeclNGen_1526_ = lean_ctor_get(v___x_1522_, 3);
v_traceState_1527_ = lean_ctor_get(v___x_1522_, 4);
v_messages_1528_ = lean_ctor_get(v___x_1522_, 6);
v_infoState_1529_ = lean_ctor_get(v___x_1522_, 7);
v_snapshotTasks_1530_ = lean_ctor_get(v___x_1522_, 8);
v_newDecls_1531_ = lean_ctor_get(v___x_1522_, 9);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1522_, 5);
lean_dec(v_unused_1542_);
v___x_1533_ = v___x_1522_;
v_isShared_1534_ = v_isSharedCheck_1541_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_newDecls_1531_);
lean_inc(v_snapshotTasks_1530_);
lean_inc(v_infoState_1529_);
lean_inc(v_messages_1528_);
lean_inc(v_traceState_1527_);
lean_inc(v_auxDeclNGen_1526_);
lean_inc(v_ngen_1525_);
lean_inc(v_nextMacroScope_1524_);
lean_inc(v_env_1523_);
lean_dec(v___x_1522_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1541_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = l_Lean_Kernel_enableDiag(v_env_1523_, v___x_1466_);
v___x_1536_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13, &l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___closed__13);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 5, v___x_1536_);
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_nextMacroScope_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_ngen_1525_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_auxDeclNGen_1526_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_traceState_1527_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_messages_1528_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_infoState_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_snapshotTasks_1530_);
lean_ctor_set(v_reuseFailAlloc_1540_, 9, v_newDecls_1531_);
v___x_1538_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_st_ref_set(v___y_1403_, v___x_1538_);
v_fileName_1468_ = v_fileName_1449_;
v_fileMap_1469_ = v_fileMap_1450_;
v_currRecDepth_1470_ = v_currRecDepth_1452_;
v_ref_1471_ = v_ref_1453_;
v_currNamespace_1472_ = v_currNamespace_1454_;
v_openDecls_1473_ = v_openDecls_1455_;
v_initHeartbeats_1474_ = v_initHeartbeats_1456_;
v_maxHeartbeats_1475_ = v_maxHeartbeats_1457_;
v_quotContext_1476_ = v_quotContext_1458_;
v_currMacroScope_1477_ = v_currMacroScope_1459_;
v_cancelTk_x3f_1478_ = v_cancelTk_x3f_1460_;
v_suppressElabErrors_1479_ = v_suppressElabErrors_1461_;
v_inheritedTraceOptions_1480_ = v_inheritedTraceOptions_1462_;
v___y_1481_ = v___y_1403_;
goto v___jp_1467_;
}
}
}
else
{
v_fileName_1468_ = v_fileName_1449_;
v_fileMap_1469_ = v_fileMap_1450_;
v_currRecDepth_1470_ = v_currRecDepth_1452_;
v_ref_1471_ = v_ref_1453_;
v_currNamespace_1472_ = v_currNamespace_1454_;
v_openDecls_1473_ = v_openDecls_1455_;
v_initHeartbeats_1474_ = v_initHeartbeats_1456_;
v_maxHeartbeats_1475_ = v_maxHeartbeats_1457_;
v_quotContext_1476_ = v_quotContext_1458_;
v_currMacroScope_1477_ = v_currMacroScope_1459_;
v_cancelTk_x3f_1478_ = v_cancelTk_x3f_1460_;
v_suppressElabErrors_1479_ = v_suppressElabErrors_1461_;
v_inheritedTraceOptions_1480_ = v_inheritedTraceOptions_1462_;
v___y_1481_ = v___y_1403_;
goto v___jp_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed(lean_object* v_a_1544_, lean_object* v_kind_1545_, lean_object* v___x_1546_, lean_object* v_a_1547_, lean_object* v___x_1548_, lean_object* v_diag_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_a_30522__boxed_1555_; uint8_t v___x_30525__boxed_1556_; lean_object* v_res_1557_; 
v_a_30522__boxed_1555_ = lean_unbox(v_a_1544_);
v___x_30525__boxed_1556_ = lean_unbox(v___x_1548_);
v_res_1557_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0(v_a_30522__boxed_1555_, v_kind_1545_, v___x_1546_, v_a_1547_, v___x_30525__boxed_1556_, v_diag_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___x_1546_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(uint8_t v_a_1563_, lean_object* v_kind_1564_, lean_object* v_as_x27_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
if (lean_obj_tag(v_as_x27_1565_) == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref(v_kind_1564_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_b_1566_);
return v___x_1572_;
}
else
{
lean_object* v_head_1573_; lean_object* v_tail_1574_; lean_object* v___x_1575_; lean_object* v_mctx_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_a_1580_; lean_object* v___x_1585_; 
lean_dec_ref(v_b_1566_);
v_head_1573_ = lean_ctor_get(v_as_x27_1565_, 0);
v_tail_1574_ = lean_ctor_get(v_as_x27_1565_, 1);
v___x_1575_ = lean_st_ref_get(v___y_1568_);
v_mctx_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_ref(v_mctx_1576_);
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v___x_1578_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0));
v___x_1585_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_1576_, v_head_1573_);
lean_dec_ref(v_mctx_1576_);
if (lean_obj_tag(v___x_1585_) == 1)
{
lean_object* v_val_1586_; lean_object* v_lctx_1587_; lean_object* v_type_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v_diag_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; 
v_val_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_val_1586_);
lean_dec_ref(v___x_1585_);
v_lctx_1587_ = lean_ctor_get(v_val_1586_, 1);
lean_inc_ref(v_lctx_1587_);
v_type_1588_ = lean_ctor_get(v_val_1586_, 2);
lean_inc_ref(v_type_1588_);
lean_dec(v_val_1586_);
v___x_1589_ = l_Lean_instantiateMVars___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__1___redArg(v_type_1588_, v___y_1568_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = lean_st_ref_get(v___y_1568_);
v_diag_1592_ = lean_ctor_get(v___x_1591_, 4);
lean_inc_ref_n(v_diag_1592_, 2);
lean_dec(v___x_1591_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__1));
v___x_1595_ = 1;
v___x_1596_ = lean_box(v_a_1563_);
v___x_1597_ = lean_box(v___x_1595_);
lean_inc_ref(v_kind_1564_);
v___f_1598_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1598_, 0, v___x_1596_);
lean_closure_set(v___f_1598_, 1, v_kind_1564_);
lean_closure_set(v___f_1598_, 2, v___x_1593_);
lean_closure_set(v___f_1598_, 3, v_a_1590_);
lean_closure_set(v___f_1598_, 4, v___x_1597_);
lean_closure_set(v___f_1598_, 5, v_diag_1592_);
v___x_1599_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__8___redArg(v_lctx_1587_, v___x_1594_, v___f_1598_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v_mctx_1602_; lean_object* v_cache_1603_; lean_object* v_zetaDeltaFVarIds_1604_; lean_object* v_postponed_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = lean_st_ref_take(v___y_1568_);
v_mctx_1602_ = lean_ctor_get(v___x_1601_, 0);
v_cache_1603_ = lean_ctor_get(v___x_1601_, 1);
v_zetaDeltaFVarIds_1604_ = lean_ctor_get(v___x_1601_, 2);
v_postponed_1605_ = lean_ctor_get(v___x_1601_, 3);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1601_, 4);
lean_dec(v_unused_1614_);
v___x_1607_ = v___x_1601_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_postponed_1605_);
lean_inc(v_zetaDeltaFVarIds_1604_);
lean_inc(v_cache_1603_);
lean_inc(v_mctx_1602_);
lean_dec(v___x_1601_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 4, v_diag_1592_);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_mctx_1602_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_cache_1603_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_zetaDeltaFVarIds_1604_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_postponed_1605_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_diag_1592_);
v___x_1610_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_st_ref_set(v___y_1568_, v___x_1610_);
v_a_1580_ = v_a_1600_;
goto v___jp_1579_;
}
}
}
else
{
lean_dec_ref(v_diag_1592_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1599_);
v_a_1580_ = v_a_1615_;
goto v___jp_1579_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_kind_1564_);
v_a_1616_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1599_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1599_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
else
{
lean_dec(v___x_1585_);
v_as_x27_1565_ = v_tail_1574_;
v_b_1566_ = v___x_1578_;
goto _start;
}
v___jp_1579_:
{
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v_kind_1564_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_a_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___x_1577_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
else
{
lean_dec(v_a_1580_);
v_as_x27_1565_ = v_tail_1574_;
v_b_1566_ = v___x_1578_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___boxed(lean_object* v_a_1625_, lean_object* v_kind_1626_, lean_object* v_as_x27_1627_, lean_object* v_b_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v_a_30770__boxed_1634_; lean_object* v_res_1635_; 
v_a_30770__boxed_1634_ = lean_unbox(v_a_1625_);
v_res_1635_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_30770__boxed_1634_, v_kind_1626_, v_as_x27_1627_, v_b_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v_as_x27_1627_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(uint8_t v_a_1636_, lean_object* v_kind_1637_, lean_object* v_goals_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg___closed__0));
v___x_1646_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_1636_, v_kind_1637_, v_goals_1638_, v___x_1645_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1659_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1659_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1659_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; 
v_fst_1651_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_fst_1651_);
lean_dec(v_a_1647_);
if (lean_obj_tag(v_fst_1651_) == 0)
{
lean_object* v___x_1653_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1644_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1644_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1657_; 
v_val_1655_ = lean_ctor_get(v_fst_1651_, 0);
lean_inc(v_val_1655_);
lean_dec_ref(v_fst_1651_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_val_1655_);
v___x_1657_ = v___x_1649_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_val_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1646_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1646_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed(lean_object* v_a_1668_, lean_object* v_kind_1669_, lean_object* v_goals_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_a_30888__boxed_1676_; lean_object* v_res_1677_; 
v_a_30888__boxed_1676_ = lean_unbox(v_a_1668_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0(v_a_30888__boxed_1676_, v_kind_1669_, v_goals_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v_goals_1670_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(uint8_t v_a_1678_, lean_object* v_val_1679_, lean_object* v_as_1680_, size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_b_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_dec(v_val_1679_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_b_1683_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v_a_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1689_ = lean_box(v_a_1678_);
v___f_1690_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1690_, 0, v___x_1689_);
v___x_1691_ = lean_box(v_a_1678_);
v___f_1692_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1692_, 0, v___x_1691_);
v___x_1693_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1694_ = lean_box(v_a_1678_);
lean_inc(v_val_1679_);
v___f_1695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1695_, 0, v_val_1679_);
lean_closure_set(v___f_1695_, 1, v___x_1694_);
lean_closure_set(v___f_1695_, 2, v___x_1693_);
lean_closure_set(v___f_1695_, 3, v___f_1690_);
v_a_1696_ = lean_array_uget_borrowed(v_as_1680_, v_i_1682_);
v___x_1697_ = lean_box(0);
lean_inc(v_a_1696_);
v___x_1698_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11(v___f_1692_, v___f_1695_, v___x_1697_, v_a_1696_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; 
lean_dec_ref(v___x_1698_);
v___x_1699_ = lean_box(0);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1682_, v___x_1700_);
v_i_1682_ = v___x_1701_;
v_b_1683_ = v___x_1699_;
goto _start;
}
else
{
lean_dec(v_val_1679_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12___boxed(lean_object* v_a_1703_, lean_object* v_val_1704_, lean_object* v_as_1705_, lean_object* v_sz_1706_, lean_object* v_i_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v_a_30953__boxed_1712_; size_t v_sz_boxed_1713_; size_t v_i_boxed_1714_; lean_object* v_res_1715_; 
v_a_30953__boxed_1712_ = lean_unbox(v_a_1703_);
v_sz_boxed_1713_ = lean_unbox_usize(v_sz_1706_);
lean_dec(v_sz_1706_);
v_i_boxed_1714_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v_a_30953__boxed_1712_, v_val_1704_, v_as_1705_, v_sz_boxed_1713_, v_i_boxed_1714_, v_b_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_as_1705_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(lean_object* v___cmdStx_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1751_; 
v___x_1720_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_linter_tacticCheckInstances;
v___x_1721_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v___x_1720_, v___y_1718_);
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1751_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1751_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_unbox(v_a_1722_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec(v_a_1722_);
v___x_1727_ = lean_box(0);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_infoState_1735_; lean_object* v_trees_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; size_t v_sz_1739_; size_t v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
lean_del_object(v___x_1724_);
v___x_1731_ = lean_st_ref_get(v___y_1718_);
v___x_1732_ = 0;
v___x_1733_ = lean_box(v___x_1732_);
v___x_1734_ = lean_st_mk_ref(v___x_1733_);
v_infoState_1735_ = lean_ctor_get(v___x_1731_, 8);
lean_inc_ref(v_infoState_1735_);
lean_dec(v___x_1731_);
v_trees_1736_ = lean_ctor_get(v_infoState_1735_, 2);
lean_inc_ref(v_trees_1736_);
lean_dec_ref(v_infoState_1735_);
v___x_1737_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1736_);
lean_dec_ref(v_trees_1736_);
v___x_1738_ = lean_box(0);
v_sz_1739_ = lean_array_size(v___x_1737_);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__12(v___x_1741_, v___x_1734_, v___x_1737_, v_sz_1739_, v___x_1740_, v___x_1738_, v___y_1717_, v___y_1718_);
lean_dec_ref(v___x_1737_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1742_, 0);
lean_dec(v_unused_1750_);
v___x_1744_ = v___x_1742_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v___x_1742_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1738_);
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1738_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0___boxed(lean_object* v___cmdStx_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances___lam__0(v___cmdStx_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___cmdStx_1752_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(lean_object* v_opt_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___redArg(v_opt_1765_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0___boxed(lean_object* v_opt_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Option_getM___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__0(v_opt_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_opt_1770_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(lean_object* v_00_u03b2_1775_, lean_object* v_m_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___redArg(v_m_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6___boxed(lean_object* v_00_u03b2_1778_, lean_object* v_m_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6(v_00_u03b2_1778_, v_m_1779_);
lean_dec_ref(v_m_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(uint8_t v_a_1781_, lean_object* v_kind_1782_, lean_object* v_as_1783_, lean_object* v_as_x27_1784_, lean_object* v_b_1785_, lean_object* v_a_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___redArg(v_a_1781_, v_kind_1782_, v_as_x27_1784_, v_b_1785_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9___boxed(lean_object* v_a_1793_, lean_object* v_kind_1794_, lean_object* v_as_1795_, lean_object* v_as_x27_1796_, lean_object* v_b_1797_, lean_object* v_a_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v_a_31132__boxed_1804_; lean_object* v_res_1805_; 
v_a_31132__boxed_1804_ = lean_unbox(v_a_1793_);
v_res_1805_ = l_List_forIn_x27_loop___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__9(v_a_31132__boxed_1804_, v_kind_1794_, v_as_1795_, v_as_x27_1796_, v_b_1797_, v_a_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v_as_x27_1796_);
lean_dec(v_as_1795_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(lean_object* v_00_u03b2_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___redArg(v_x_1807_, v_x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6(v_00_u03b2_1810_, v_x_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec_ref(v_x_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7(lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7___redArg(v_x_1815_, v_x_1816_, v_x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(lean_object* v_00_u03c3_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_map_1821_, lean_object* v_init_1822_, lean_object* v_f_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___redArg(v_map_1821_, v_init_1822_, v_f_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_map_1827_, lean_object* v_init_1828_, lean_object* v_f_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8(v_00_u03c3_1825_, v_00_u03b2_1826_, v_map_1827_, v_init_1828_, v_f_1829_);
lean_dec_ref(v_map_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(lean_object* v_00_u03c3_1831_, lean_object* v_00_u03b2_1832_, lean_object* v_map_1833_, lean_object* v_f_1834_, lean_object* v_init_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___redArg(v_map_1833_, v_f_1834_, v_init_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10___boxed(lean_object* v_00_u03c3_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_map_1839_, lean_object* v_f_1840_, lean_object* v_init_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10(v_00_u03c3_1837_, v_00_u03b2_1838_, v_map_1839_, v_f_1840_, v_init_1841_);
lean_dec_ref(v_map_1839_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(lean_object* v_00_u03b1_1843_, lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___redArg(v_msg_1844_, v___y_1845_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_msg_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__23(v_00_u03b1_1849_, v_msg_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(lean_object* v_00_u03b1_1855_, lean_object* v_preNode_1856_, lean_object* v_postNode_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___redArg(v_preNode_1856_, v_postNode_1857_, v_x_1858_, v_x_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_preNode_1865_, lean_object* v_postNode_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17(v_00_u03b1_1864_, v_preNode_1865_, v_postNode_1866_, v_x_1867_, v_x_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1873_, lean_object* v_x_1874_, size_t v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___redArg(v_x_1874_, v_x_1875_, v_x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
size_t v_x_31204__boxed_1882_; lean_object* v_res_1883_; 
v_x_31204__boxed_1882_ = lean_unbox_usize(v_x_1880_);
lean_dec(v_x_1880_);
v_res_1883_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8(v_00_u03b2_1878_, v_x_1879_, v_x_31204__boxed_1882_, v_x_1881_);
lean_dec(v_x_1881_);
lean_dec_ref(v_x_1879_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_1884_, lean_object* v_x_1885_, size_t v_x_1886_, size_t v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___redArg(v_x_1885_, v_x_1886_, v_x_1887_, v_x_1888_, v_x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
size_t v_x_31215__boxed_1897_; size_t v_x_31216__boxed_1898_; lean_object* v_res_1899_; 
v_x_31215__boxed_1897_ = lean_unbox_usize(v_x_1893_);
lean_dec(v_x_1893_);
v_x_31216__boxed_1898_ = lean_unbox_usize(v_x_1894_);
lean_dec(v_x_1894_);
v_res_1899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10(v_00_u03b2_1891_, v_x_1892_, v_x_31215__boxed_1897_, v_x_31216__boxed_1898_, v_x_1895_, v_x_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12___redArg(lean_object* v_map_1900_, lean_object* v_f_1901_, lean_object* v_init_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_1901_, v_map_1900_, v_init_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12(lean_object* v_00_u03c3_1904_, lean_object* v_00_u03c3_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_map_1907_, lean_object* v_f_1908_, lean_object* v_init_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_1908_, v_map_1907_, v_init_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(lean_object* v_map_1911_, lean_object* v_f_1912_, lean_object* v_init_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1912_, v_map_1911_, v_init_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_map_1915_, lean_object* v_f_1916_, lean_object* v_init_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___redArg(v_map_1915_, v_f_1916_, v_init_1917_);
lean_dec_ref(v_map_1915_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(lean_object* v_00_u03c3_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_map_1921_, lean_object* v_f_1922_, lean_object* v_init_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_1922_, v_map_1921_, v_init_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03c3_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_map_1927_, lean_object* v_f_1928_, lean_object* v_init_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15(v_00_u03c3_1925_, v_00_u03b2_1926_, v_map_1927_, v_f_1928_, v_init_1929_);
lean_dec_ref(v_map_1927_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(lean_object* v_msgData_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___redArg(v_msgData_1931_, v___y_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28___boxed(lean_object* v_msgData_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__10_spec__15_spec__20_spec__28(v_msgData_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(lean_object* v_00_u03b1_1941_, lean_object* v_preNode_1942_, lean_object* v_postNode_1943_, lean_object* v___x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___redArg(v_preNode_1942_, v_postNode_1943_, v___x_1944_, v_x_1945_, v_x_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_preNode_1952_, lean_object* v_postNode_1953_, lean_object* v___x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__11_spec__17_spec__24(v_00_u03b1_1951_, v_preNode_1952_, v_postNode_1953_, v___x_1954_, v_x_1955_, v_x_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b2_1961_, lean_object* v_keys_1962_, lean_object* v_vals_1963_, lean_object* v_heq_1964_, lean_object* v_i_1965_, lean_object* v_k_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___redArg(v_keys_1962_, v_vals_1963_, v_i_1965_, v_k_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b2_1968_, lean_object* v_keys_1969_, lean_object* v_vals_1970_, lean_object* v_heq_1971_, lean_object* v_i_1972_, lean_object* v_k_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__6_spec__8_spec__15(v_00_u03b2_1968_, v_keys_1969_, v_vals_1970_, v_heq_1971_, v_i_1972_, v_k_1973_);
lean_dec(v_k_1973_);
lean_dec_ref(v_vals_1970_);
lean_dec_ref(v_keys_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18(lean_object* v_00_u03b2_1975_, lean_object* v_n_1976_, lean_object* v_k_1977_, lean_object* v_v_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18___redArg(v_n_1976_, v_k_1977_, v_v_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(lean_object* v_00_u03b2_1980_, size_t v_depth_1981_, lean_object* v_keys_1982_, lean_object* v_vals_1983_, lean_object* v_heq_1984_, lean_object* v_i_1985_, lean_object* v_entries_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___redArg(v_depth_1981_, v_keys_1982_, v_vals_1983_, v_i_1985_, v_entries_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19___boxed(lean_object* v_00_u03b2_1988_, lean_object* v_depth_1989_, lean_object* v_keys_1990_, lean_object* v_vals_1991_, lean_object* v_heq_1992_, lean_object* v_i_1993_, lean_object* v_entries_1994_){
_start:
{
size_t v_depth_boxed_1995_; lean_object* v_res_1996_; 
v_depth_boxed_1995_ = lean_unbox_usize(v_depth_1989_);
lean_dec(v_depth_1989_);
v_res_1996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__19(v_00_u03b2_1988_, v_depth_boxed_1995_, v_keys_1990_, v_vals_1991_, v_heq_1992_, v_i_1993_, v_entries_1994_);
lean_dec_ref(v_vals_1991_);
lean_dec_ref(v_keys_1990_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22(lean_object* v_00_u03c3_1997_, lean_object* v_00_u03c3_1998_, lean_object* v_00_u03b1_1999_, lean_object* v_00_u03b2_2000_, lean_object* v_f_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22___redArg(v_f_2001_, v_x_2002_, v_x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(lean_object* v_00_u03c3_2005_, lean_object* v_00_u03b1_2006_, lean_object* v_00_u03b2_2007_, lean_object* v_f_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___redArg(v_f_2008_, v_x_2009_, v_x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25___boxed(lean_object* v_00_u03c3_2012_, lean_object* v_00_u03b1_2013_, lean_object* v_00_u03b2_2014_, lean_object* v_f_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25(v_00_u03c3_2012_, v_00_u03b1_2013_, v_00_u03b2_2014_, v_f_2015_, v_x_2016_, v_x_2017_);
lean_dec_ref(v_x_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__7_spec__10_spec__18_spec__24___redArg(v_x_2020_, v_x_2021_, v_x_2022_, v_x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(lean_object* v_00_u03b1_2025_, lean_object* v_00_u03b2_2026_, lean_object* v_00_u03c3_2027_, lean_object* v_00_u03c3_2028_, lean_object* v_f_2029_, lean_object* v_as_2030_, size_t v_i_2031_, size_t v_stop_2032_, lean_object* v_b_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___redArg(v_f_2029_, v_as_2030_, v_i_2031_, v_stop_2032_, v_b_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_00_u03b2_2036_, lean_object* v_00_u03c3_2037_, lean_object* v_00_u03c3_2038_, lean_object* v_f_2039_, lean_object* v_as_2040_, lean_object* v_i_2041_, lean_object* v_stop_2042_, lean_object* v_b_2043_){
_start:
{
size_t v_i_boxed_2044_; size_t v_stop_boxed_2045_; lean_object* v_res_2046_; 
v_i_boxed_2044_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_stop_boxed_2045_ = lean_unbox_usize(v_stop_2042_);
lean_dec(v_stop_2042_);
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__28(v_00_u03b1_2035_, v_00_u03b2_2036_, v_00_u03c3_2037_, v_00_u03c3_2038_, v_f_2039_, v_as_2040_, v_i_boxed_2044_, v_stop_boxed_2045_, v_b_2043_);
lean_dec_ref(v_as_2040_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(lean_object* v_00_u03c3_2047_, lean_object* v_00_u03c3_2048_, lean_object* v_00_u03b1_2049_, lean_object* v_00_u03b2_2050_, lean_object* v_f_2051_, lean_object* v_keys_2052_, lean_object* v_vals_2053_, lean_object* v_heq_2054_, lean_object* v_i_2055_, lean_object* v_acc_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___redArg(v_f_2051_, v_keys_2052_, v_vals_2053_, v_i_2055_, v_acc_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29___boxed(lean_object* v_00_u03c3_2058_, lean_object* v_00_u03c3_2059_, lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_f_2062_, lean_object* v_keys_2063_, lean_object* v_vals_2064_, lean_object* v_heq_2065_, lean_object* v_i_2066_, lean_object* v_acc_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_subCounters___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__5_spec__8_spec__12_spec__22_spec__29(v_00_u03c3_2058_, v_00_u03c3_2059_, v_00_u03b1_2060_, v_00_u03b2_2061_, v_f_2062_, v_keys_2063_, v_vals_2064_, v_heq_2065_, v_i_2066_, v_acc_2067_);
lean_dec_ref(v_vals_2064_);
lean_dec_ref(v_keys_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_00_u03c3_2071_, lean_object* v_f_2072_, lean_object* v_as_2073_, size_t v_i_2074_, size_t v_stop_2075_, lean_object* v_b_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___redArg(v_f_2072_, v_as_2073_, v_i_2074_, v_stop_2075_, v_b_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_00_u03c3_2080_, lean_object* v_f_2081_, lean_object* v_as_2082_, lean_object* v_i_2083_, lean_object* v_stop_2084_, lean_object* v_b_2085_){
_start:
{
size_t v_i_boxed_2086_; size_t v_stop_boxed_2087_; lean_object* v_res_2088_; 
v_i_boxed_2086_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_stop_boxed_2087_ = lean_unbox_usize(v_stop_2084_);
lean_dec(v_stop_2084_);
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__32(v_00_u03b1_2078_, v_00_u03b2_2079_, v_00_u03c3_2080_, v_f_2081_, v_as_2082_, v_i_boxed_2086_, v_stop_boxed_2087_, v_b_2085_);
lean_dec_ref(v_as_2082_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(lean_object* v_00_u03c3_2089_, lean_object* v_00_u03b1_2090_, lean_object* v_00_u03b2_2091_, lean_object* v_f_2092_, lean_object* v_keys_2093_, lean_object* v_vals_2094_, lean_object* v_heq_2095_, lean_object* v_i_2096_, lean_object* v_acc_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___redArg(v_f_2092_, v_keys_2093_, v_vals_2094_, v_i_2096_, v_acc_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2099_, lean_object* v_00_u03b1_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_f_2102_, lean_object* v_keys_2103_, lean_object* v_vals_2104_, lean_object* v_heq_2105_, lean_object* v_i_2106_, lean_object* v_acc_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00__private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances_spec__6_spec__10_spec__15_spec__25_spec__33(v_00_u03c3_2099_, v_00_u03b1_2100_, v_00_u03b2_2101_, v_f_2102_, v_keys_2103_, v_vals_2104_, v_heq_2105_, v_i_2106_, v_acc_2107_);
lean_dec_ref(v_vals_2104_);
lean_dec_ref(v_keys_2103_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_tacticCheckInstances));
v___x_2111_ = l_Lean_Elab_Command_addLinter(v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2____boxed(lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_490307252____hygCtx___hyg_2_();
return v_res_2113_;
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
res = l___private_Lean_Linter_TacticTypeCheck_0__Lean_Linter_initFn_00___x40_Lean_Linter_TacticTypeCheck_4117896218____hygCtx___hyg_4_();
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
