// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.ShowState
// Imports: public import Lean.Elab.Tactic.Grind.Filter import Lean.Meta.Tactic.Grind.PP import Lean.Meta.Tactic.Grind.EMatchTheoremParam import Lean.Meta.Tactic.Grind.Split
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_ppEqc(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabFilter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_ppExprArray(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getLocalTheoremAnchors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_anchorToString(lean_object*, uint64_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_evalGrindTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Filter_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "facts"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 104, 51, 228, 98, 188, 251, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Asserted facts"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no facts"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindFilter"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "showAsserted"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value),LEAN_SCALAR_PTR_LITERAL(19, 9, 52, 210, 246, 83, 42, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ShowState"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 25, 164, 64, 171, 22, 6, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 19, 40, 233, 34, 161, 117, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 78, 84, 89, 236, 187, 159, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 245, 207, 60, 37, 134, 98, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(38, 49, 162, 201, 131, 208, 27, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 71, 128, 234, 115, 187, 122, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalShowAsserted"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(200, 208, 203, 159, 70, 103, 81, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "props"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 109, 51, 84, 90, 92, 70, 19)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " propositions"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "no "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTrue"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 221, 230, 107, 62, 158, 128, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(55, 133, 155, 61, 50, 240, 42, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowTrue"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 147, 90, 193, 92, 229, 28, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showFalse"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 23, 10, 157, 249, 80, 147, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalShowFalse"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 252, 51, 157, 108, 134, 132, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eqc"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 40, 20, 175, 160, 100, 35, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Equivalence classes"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "others"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no equivalence classes"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showEqcs"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 3, 250, 60, 240, 18, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowEqcs"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 119, 28, 131, 183, 128, 4, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Grind state"};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showState"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 80, 82, 248, 223, 67, 174, 140)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalShowState"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 96, 229, 223, 171, 103, 139, 248)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 90, 54, 167, 41, 130, 106, 252)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "splits"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 201, 206, 84, 124, 223, 95, 96)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Case split candidates"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "no case splits"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showCases"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 129, 48, 5, 176, 175, 163, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalShowCases"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 115, 106, 2, 47, 9, 123, 219)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 106, 229, 125, 19, 158, 75, 156)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "thms"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 43, 249, 113, 45, 82, 7, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Local theorems"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "showLocalThms"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 164, 136, 213, 0, 240, 18, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalShowLocalThms"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 150, 229, 48, 187, 110, 180, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 150, 74, 14, 71, 142, 109, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalShowTerm"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 168, 61, 18, 39, 162, 48, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(lean_object* v_filter_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_, lean_object* v_b_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_a_10_; uint8_t v___x_14_; 
v___x_14_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
lean_inc(v_filter_1_);
lean_inc(v___x_15_);
v___x_16_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v___x_15_, v_filter_1_, v___y_6_, v___y_7_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; uint8_t v___x_18_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_16_, 1);
v___x_18_ = lean_unbox(v_a_17_);
lean_dec(v_a_17_);
if (v___x_18_ == 0)
{
v_a_10_ = v_b_5_;
goto v___jp_9_;
}
else
{
lean_object* v___x_19_; 
lean_inc(v___x_15_);
v___x_19_ = lean_array_push(v_b_5_, v___x_15_);
v_a_10_ = v___x_19_;
goto v___jp_9_;
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec_ref(v_b_5_);
lean_dec(v_filter_1_);
v_a_20_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_16_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_16_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
else
{
lean_object* v___x_28_; 
lean_dec(v_filter_1_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v_b_5_);
return v___x_28_;
}
v___jp_9_:
{
size_t v___x_11_; size_t v___x_12_; 
v___x_11_ = ((size_t)1ULL);
v___x_12_ = lean_usize_add(v_i_3_, v___x_11_);
v_i_3_ = v___x_12_;
v_b_5_ = v_a_10_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg___boxed(lean_object* v_filter_29_, lean_object* v_as_30_, lean_object* v_i_31_, lean_object* v_stop_32_, lean_object* v_b_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
size_t v_i_boxed_37_; size_t v_stop_boxed_38_; lean_object* v_res_39_; 
v_i_boxed_37_ = lean_unbox_usize(v_i_31_);
lean_dec(v_i_31_);
v_stop_boxed_38_ = lean_unbox_usize(v_stop_32_);
lean_dec(v_stop_32_);
v_res_39_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_29_, v_as_30_, v_i_boxed_37_, v_stop_boxed_38_, v_b_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v_as_30_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(lean_object* v_filter_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; lean_object* v_toGoalState_55_; lean_object* v_facts_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_54_ = lean_st_ref_get(v___y_43_);
v_toGoalState_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_toGoalState_55_);
lean_dec(v___x_54_);
v_facts_56_ = lean_ctor_get(v_toGoalState_55_, 10);
lean_inc_ref(v_facts_56_);
lean_dec_ref(v_toGoalState_55_);
v___x_57_ = l_Lean_PersistentArray_toArray___redArg(v_facts_56_);
lean_dec_ref(v_facts_56_);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_array_get_size(v___x_57_);
v___x_60_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0));
v___x_61_ = lean_nat_dec_lt(v___x_58_, v___x_59_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
lean_dec_ref(v___x_57_);
lean_dec(v_filter_42_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = lean_nat_dec_le(v___x_59_, v___x_59_);
if (v___x_63_ == 0)
{
if (v___x_61_ == 0)
{
lean_object* v___x_64_; 
lean_dec_ref(v___x_57_);
lean_dec(v_filter_42_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_60_);
return v___x_64_;
}
else
{
size_t v___x_65_; size_t v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((size_t)0ULL);
v___x_66_ = lean_usize_of_nat(v___x_59_);
v___x_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_42_, v___x_57_, v___x_65_, v___x_66_, v___x_60_, v___y_43_, v___y_50_);
lean_dec_ref(v___x_57_);
return v___x_67_;
}
}
else
{
size_t v___x_68_; size_t v___x_69_; lean_object* v___x_70_; 
v___x_68_ = ((size_t)0ULL);
v___x_69_ = lean_usize_of_nat(v___x_59_);
v___x_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_42_, v___x_57_, v___x_68_, v___x_69_, v___x_60_, v___y_43_, v___y_50_);
lean_dec_ref(v___x_57_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed(lean_object* v_filter_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(v_filter_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec(v___y_72_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(lean_object* v_filter_92_, uint8_t v_collapsed_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_101_, 0, v_filter_92_);
v___x_102_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_101_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_122_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_122_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_122_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_122_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = lean_array_get_size(v_a_103_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_nat_dec_eq(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1));
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2));
v___x_112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4));
v___x_113_ = l_Lean_Meta_Grind_ppExprArray(v___x_110_, v___x_111_, v_a_103_, v___x_112_, v_collapsed_93_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_114_);
v___x_116_ = v___x_105_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v_a_103_);
v___x_118_ = lean_box(0);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_118_);
v___x_120_ = v___x_105_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_102_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_102_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___boxed(lean_object* v_filter_131_, lean_object* v_collapsed_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_collapsed_boxed_140_; lean_object* v_res_141_; 
v_collapsed_boxed_140_ = lean_unbox(v_collapsed_132_);
v_res_141_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_filter_131_, v_collapsed_boxed_140_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(lean_object* v_filter_142_, uint8_t v_collapsed_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_filter_142_, v_collapsed_143_, v_a_144_, v_a_145_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___boxed(lean_object* v_filter_154_, lean_object* v_collapsed_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
uint8_t v_collapsed_boxed_165_; lean_object* v_res_166_; 
v_collapsed_boxed_165_ = lean_unbox(v_collapsed_155_);
v_res_166_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(v_filter_154_, v_collapsed_boxed_165_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(lean_object* v_filter_167_, lean_object* v_as_168_, size_t v_i_169_, size_t v_stop_170_, lean_object* v_b_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_167_, v_as_168_, v_i_169_, v_stop_170_, v_b_171_, v___y_172_, v___y_179_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___boxed(lean_object* v_filter_184_, lean_object* v_as_185_, lean_object* v_i_186_, lean_object* v_stop_187_, lean_object* v_b_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
size_t v_i_boxed_200_; size_t v_stop_boxed_201_; lean_object* v_res_202_; 
v_i_boxed_200_ = lean_unbox_usize(v_i_186_);
lean_dec(v_i_186_);
v_stop_boxed_201_ = lean_unbox_usize(v_stop_187_);
lean_dec(v_stop_187_);
v_res_202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(v_filter_184_, v_as_185_, v_i_boxed_200_, v_stop_boxed_201_, v_b_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v_as_185_);
return v_res_202_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_box(0);
v___x_204_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg(){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___boxed(lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(lean_object* v_00_u03b1_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___boxed(lean_object* v_00_u03b1_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(v_00_u03b1_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(lean_object* v_msgData_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_env_240_; lean_object* v___x_241_; lean_object* v_toCold_242_; lean_object* v_mctx_243_; lean_object* v_lctx_244_; lean_object* v_options_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_239_ = lean_st_ref_get(v___y_237_);
v_env_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_env_240_);
lean_dec(v___x_239_);
v___x_241_ = lean_st_ref_get(v___y_235_);
v_toCold_242_ = lean_ctor_get(v___y_236_, 0);
v_mctx_243_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_mctx_243_);
lean_dec(v___x_241_);
v_lctx_244_ = lean_ctor_get(v___y_234_, 2);
v_options_245_ = lean_ctor_get(v_toCold_242_, 2);
lean_inc_ref(v_options_245_);
lean_inc_ref(v_lctx_244_);
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_env_240_);
lean_ctor_set(v___x_246_, 1, v_mctx_243_);
lean_ctor_set(v___x_246_, 2, v_lctx_244_);
lean_ctor_set(v___x_246_, 3, v_options_245_);
v___x_247_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_msgData_233_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2___boxed(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(v_msgData_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_ref_262_ = lean_ctor_get(v___y_259_, 2);
v___x_263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_inc(v_ref_262_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_262_);
lean_ctor_set(v___x_268_, 1, v_a_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg___boxed(lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(lean_object* v_opts_280_, lean_object* v_opt_281_){
_start:
{
lean_object* v_name_282_; lean_object* v_defValue_283_; lean_object* v_map_284_; lean_object* v___x_285_; 
v_name_282_ = lean_ctor_get(v_opt_281_, 0);
v_defValue_283_ = lean_ctor_get(v_opt_281_, 1);
v_map_284_ = lean_ctor_get(v_opts_280_, 0);
v___x_285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_284_, v_name_282_);
if (lean_obj_tag(v___x_285_) == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_unbox(v_defValue_283_);
return v___x_286_;
}
else
{
lean_object* v_val_287_; 
v_val_287_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_285_, 1);
if (lean_obj_tag(v_val_287_) == 1)
{
uint8_t v_v_288_; 
v_v_288_ = lean_ctor_get_uint8(v_val_287_, 0);
lean_dec_ref_known(v_val_287_, 0);
return v_v_288_;
}
else
{
uint8_t v___x_289_; 
lean_dec(v_val_287_);
v___x_289_ = lean_unbox(v_defValue_283_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_opts_290_, lean_object* v_opt_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(v_opts_290_, v_opt_291_);
lean_dec_ref(v_opt_291_);
lean_dec_ref(v_opts_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_302_, uint8_t v___y_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 1)
{
lean_object* v_pre_305_; 
v_pre_305_ = lean_ctor_get(v_x_304_, 0);
switch(lean_obj_tag(v_pre_305_))
{
case 1:
{
lean_object* v_pre_306_; 
v_pre_306_ = lean_ctor_get(v_pre_305_, 0);
switch(lean_obj_tag(v_pre_306_))
{
case 0:
{
lean_object* v_str_307_; lean_object* v_str_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_str_307_ = lean_ctor_get(v_x_304_, 1);
v_str_308_ = lean_ctor_get(v_pre_305_, 1);
v___x_309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_310_ = lean_string_dec_eq(v_str_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_312_ = lean_string_dec_eq(v_str_308_, v___x_311_);
if (v___x_312_ == 0)
{
return v___x_312_;
}
else
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_314_ = lean_string_dec_eq(v_str_307_, v___x_313_);
if (v___x_314_ == 0)
{
return v___x_314_;
}
else
{
return v_suppressElabErrors_302_;
}
}
}
else
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_316_ = lean_string_dec_eq(v_str_307_, v___x_315_);
if (v___x_316_ == 0)
{
return v___x_316_;
}
else
{
return v_suppressElabErrors_302_;
}
}
}
case 1:
{
lean_object* v_pre_317_; 
v_pre_317_ = lean_ctor_get(v_pre_306_, 0);
if (lean_obj_tag(v_pre_317_) == 0)
{
lean_object* v_str_318_; lean_object* v_str_319_; lean_object* v_str_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_str_318_ = lean_ctor_get(v_x_304_, 1);
v_str_319_ = lean_ctor_get(v_pre_305_, 1);
v_str_320_ = lean_ctor_get(v_pre_306_, 1);
v___x_321_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_322_ = lean_string_dec_eq(v_str_320_, v___x_321_);
if (v___x_322_ == 0)
{
return v___x_322_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_324_ = lean_string_dec_eq(v_str_319_, v___x_323_);
if (v___x_324_ == 0)
{
return v___x_324_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_326_ = lean_string_dec_eq(v_str_318_, v___x_325_);
if (v___x_326_ == 0)
{
return v___x_326_;
}
else
{
return v_suppressElabErrors_302_;
}
}
}
}
else
{
return v___y_303_;
}
}
default: 
{
return v___y_303_;
}
}
}
case 0:
{
lean_object* v_str_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_str_327_ = lean_ctor_get(v_x_304_, 1);
v___x_328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_329_ = lean_string_dec_eq(v_str_327_, v___x_328_);
if (v___x_329_ == 0)
{
return v___x_329_;
}
else
{
return v_suppressElabErrors_302_;
}
}
default: 
{
return v___y_303_;
}
}
}
else
{
return v___y_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_330_, lean_object* v___y_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_suppressElabErrors_boxed_333_; uint8_t v___y_6544__boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_suppressElabErrors_boxed_333_ = lean_unbox(v_suppressElabErrors_330_);
v___y_6544__boxed_334_ = lean_unbox(v___y_331_);
v_res_335_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_333_, v___y_6544__boxed_334_, v_x_332_);
lean_dec(v_x_332_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_338_, lean_object* v_msgData_339_, uint8_t v_severity_340_, uint8_t v_isSilent_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v_toCold_355_; lean_object* v___y_356_; lean_object* v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; uint8_t v___y_391_; lean_object* v___y_392_; lean_object* v___y_412_; lean_object* v___y_413_; uint8_t v___y_414_; uint8_t v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_422_; uint8_t v___y_423_; uint8_t v___y_424_; uint8_t v___x_435_; uint8_t v___y_437_; uint8_t v___y_438_; uint8_t v___y_439_; uint8_t v___y_441_; uint8_t v___x_449_; 
v___x_435_ = 2;
v___x_449_ = l_Lean_instBEqMessageSeverity_beq(v_severity_340_, v___x_435_);
if (v___x_449_ == 0)
{
v___y_441_ = v___x_449_;
goto v___jp_440_;
}
else
{
uint8_t v___x_450_; 
lean_inc_ref(v_msgData_339_);
v___x_450_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_339_);
v___y_441_ = v___x_450_;
goto v___jp_440_;
}
v___jp_347_:
{
lean_object* v_currNamespace_357_; lean_object* v_openDecls_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_env_363_; lean_object* v_nextMacroScope_364_; lean_object* v_ngen_365_; lean_object* v_auxDeclNGen_366_; lean_object* v_traceState_367_; lean_object* v_cache_368_; lean_object* v_recordedDeps_369_; lean_object* v_messages_370_; lean_object* v_infoState_371_; lean_object* v_snapshotTasks_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_383_; 
v_currNamespace_357_ = lean_ctor_get(v_toCold_355_, 4);
v_openDecls_358_ = lean_ctor_get(v_toCold_355_, 5);
lean_inc(v_openDecls_358_);
lean_inc(v_currNamespace_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_currNamespace_357_);
lean_ctor_set(v___x_359_, 1, v_openDecls_358_);
v___x_360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___y_352_);
lean_inc_ref(v___y_351_);
lean_inc_ref(v___y_350_);
v___x_361_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_361_, 0, v___y_350_);
lean_ctor_set(v___x_361_, 1, v___y_353_);
lean_ctor_set(v___x_361_, 2, v___y_354_);
lean_ctor_set(v___x_361_, 3, v___y_351_);
lean_ctor_set(v___x_361_, 4, v___x_360_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5, v___y_349_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5 + 1, v___y_348_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5 + 2, v_isSilent_341_);
v___x_362_ = lean_st_ref_take(v___y_356_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
v_nextMacroScope_364_ = lean_ctor_get(v___x_362_, 1);
v_ngen_365_ = lean_ctor_get(v___x_362_, 2);
v_auxDeclNGen_366_ = lean_ctor_get(v___x_362_, 3);
v_traceState_367_ = lean_ctor_get(v___x_362_, 4);
v_cache_368_ = lean_ctor_get(v___x_362_, 5);
v_recordedDeps_369_ = lean_ctor_get(v___x_362_, 6);
v_messages_370_ = lean_ctor_get(v___x_362_, 7);
v_infoState_371_ = lean_ctor_get(v___x_362_, 8);
v_snapshotTasks_372_ = lean_ctor_get(v___x_362_, 9);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_383_ == 0)
{
v___x_374_ = v___x_362_;
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_snapshotTasks_372_);
lean_inc(v_infoState_371_);
lean_inc(v_messages_370_);
lean_inc(v_recordedDeps_369_);
lean_inc(v_cache_368_);
lean_inc(v_traceState_367_);
lean_inc(v_auxDeclNGen_366_);
lean_inc(v_ngen_365_);
lean_inc(v_nextMacroScope_364_);
lean_inc(v_env_363_);
lean_dec(v___x_362_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_376_ = lean_box(0);
v___x_377_ = l_Lean_MessageLog_add(v___x_361_, v_messages_370_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 7, v___x_377_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_env_363_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_nextMacroScope_364_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_ngen_365_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_auxDeclNGen_366_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_traceState_367_);
lean_ctor_set(v_reuseFailAlloc_382_, 5, v_cache_368_);
lean_ctor_set(v_reuseFailAlloc_382_, 6, v_recordedDeps_369_);
lean_ctor_set(v_reuseFailAlloc_382_, 7, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_382_, 8, v_infoState_371_);
lean_ctor_set(v_reuseFailAlloc_382_, 9, v_snapshotTasks_372_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_st_ref_put(v___y_356_, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_376_);
return v___x_381_;
}
}
}
v___jp_384_:
{
lean_object* v_fileName_393_; lean_object* v_fileMap_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_410_; 
v_fileName_393_ = lean_ctor_get(v___y_390_, 0);
v_fileMap_394_ = lean_ctor_get(v___y_390_, 1);
v___x_395_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_339_);
v___x_396_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(v___x_395_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_410_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_410_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_410_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_inc_ref_n(v_fileMap_394_, 2);
v___x_401_ = l_Lean_FileMap_toPosition(v_fileMap_394_, v___y_389_);
lean_dec(v___y_389_);
v___x_402_ = l_Lean_FileMap_toPosition(v_fileMap_394_, v___y_392_);
lean_dec(v___y_392_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
if (v___y_391_ == 0)
{
lean_del_object(v___x_399_);
lean_dec_ref(v___y_385_);
v___y_348_ = v___y_387_;
v___y_349_ = v___y_388_;
v___y_350_ = v_fileName_393_;
v___y_351_ = v___x_404_;
v___y_352_ = v_a_397_;
v___y_353_ = v___x_401_;
v___y_354_ = v___x_403_;
v_toCold_355_ = v___y_386_;
v___y_356_ = v___y_345_;
goto v___jp_347_;
}
else
{
uint8_t v___x_405_; 
lean_inc(v_a_397_);
v___x_405_ = l_Lean_MessageData_hasTag(v___y_385_, v_a_397_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
lean_dec_ref_known(v___x_403_, 1);
lean_dec_ref(v___x_401_);
lean_dec(v_a_397_);
v___x_406_ = lean_box(0);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_406_);
v___x_408_ = v___x_399_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
else
{
lean_del_object(v___x_399_);
v___y_348_ = v___y_387_;
v___y_349_ = v___y_388_;
v___y_350_ = v_fileName_393_;
v___y_351_ = v___x_404_;
v___y_352_ = v_a_397_;
v___y_353_ = v___x_401_;
v___y_354_ = v___x_403_;
v_toCold_355_ = v___y_386_;
v___y_356_ = v___y_345_;
goto v___jp_347_;
}
}
}
}
v___jp_411_:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Syntax_getTailPos_x3f(v___y_417_, v___y_416_);
lean_dec(v___y_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_inc(v___y_418_);
v___y_385_ = v___y_412_;
v___y_386_ = v___y_413_;
v___y_387_ = v___y_415_;
v___y_388_ = v___y_416_;
v___y_389_ = v___y_418_;
v___y_390_ = v___y_413_;
v___y_391_ = v___y_414_;
v___y_392_ = v___y_418_;
goto v___jp_384_;
}
else
{
lean_object* v_val_420_; 
v_val_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v___x_419_, 1);
v___y_385_ = v___y_412_;
v___y_386_ = v___y_413_;
v___y_387_ = v___y_415_;
v___y_388_ = v___y_416_;
v___y_389_ = v___y_418_;
v___y_390_ = v___y_413_;
v___y_391_ = v___y_414_;
v___y_392_ = v_val_420_;
goto v___jp_384_;
}
}
v___jp_421_:
{
lean_object* v_toCold_425_; lean_object* v_ref_426_; uint8_t v_suppressElabErrors_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___f_430_; lean_object* v_ref_431_; lean_object* v___x_432_; 
v_toCold_425_ = lean_ctor_get(v___y_344_, 0);
v_ref_426_ = lean_ctor_get(v___y_344_, 2);
v_suppressElabErrors_427_ = lean_ctor_get_uint8(v___y_344_, sizeof(void*)*3 + 2);
v___x_428_ = lean_box(v_suppressElabErrors_427_);
v___x_429_ = lean_box(v___y_422_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_430_, 0, v___x_428_);
lean_closure_set(v___f_430_, 1, v___x_429_);
v_ref_431_ = l_Lean_replaceRef(v_ref_338_, v_ref_426_);
v___x_432_ = l_Lean_Syntax_getPos_x3f(v_ref_431_, v___y_423_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___y_412_ = v___f_430_;
v___y_413_ = v_toCold_425_;
v___y_414_ = v_suppressElabErrors_427_;
v___y_415_ = v___y_424_;
v___y_416_ = v___y_423_;
v___y_417_ = v_ref_431_;
v___y_418_ = v___x_433_;
goto v___jp_411_;
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_432_, 1);
v___y_412_ = v___f_430_;
v___y_413_ = v_toCold_425_;
v___y_414_ = v_suppressElabErrors_427_;
v___y_415_ = v___y_424_;
v___y_416_ = v___y_423_;
v___y_417_ = v_ref_431_;
v___y_418_ = v_val_434_;
goto v___jp_411_;
}
}
v___jp_436_:
{
if (v___y_439_ == 0)
{
v___y_422_ = v___y_437_;
v___y_423_ = v___y_438_;
v___y_424_ = v_severity_340_;
goto v___jp_421_;
}
else
{
v___y_422_ = v___y_437_;
v___y_423_ = v___y_438_;
v___y_424_ = v___x_435_;
goto v___jp_421_;
}
}
v___jp_440_:
{
if (v___y_441_ == 0)
{
uint8_t v___x_442_; uint8_t v___x_443_; 
v___x_442_ = 1;
v___x_443_ = l_Lean_instBEqMessageSeverity_beq(v_severity_340_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_437_ = v___y_441_;
v___y_438_ = v___y_441_;
v___y_439_ = v___x_443_;
goto v___jp_436_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_344_);
v___x_445_ = l_Lean_warningAsError;
v___x_446_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(v___x_444_, v___x_445_);
lean_dec_ref(v___x_444_);
v___y_437_ = v___y_441_;
v___y_438_ = v___y_441_;
v___y_439_ = v___x_446_;
goto v___jp_436_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v_msgData_339_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_451_, lean_object* v_msgData_452_, lean_object* v_severity_453_, lean_object* v_isSilent_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v_severity_boxed_460_; uint8_t v_isSilent_boxed_461_; lean_object* v_res_462_; 
v_severity_boxed_460_ = lean_unbox(v_severity_453_);
v_isSilent_boxed_461_ = lean_unbox(v_isSilent_454_);
v_res_462_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_451_, v_msgData_452_, v_severity_boxed_460_, v_isSilent_boxed_461_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v_ref_451_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(lean_object* v_msgData_463_, uint8_t v_severity_464_, uint8_t v_isSilent_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_ref_475_; lean_object* v___x_476_; 
v_ref_475_ = lean_ctor_get(v___y_472_, 2);
v___x_476_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_475_, v_msgData_463_, v_severity_464_, v_isSilent_465_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0___boxed(lean_object* v_msgData_477_, lean_object* v_severity_478_, lean_object* v_isSilent_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v_severity_boxed_489_; uint8_t v_isSilent_boxed_490_; lean_object* v_res_491_; 
v_severity_boxed_489_ = lean_unbox(v_severity_478_);
v_isSilent_boxed_490_ = lean_unbox(v_isSilent_479_);
v_res_491_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(v_msgData_477_, v_severity_boxed_489_, v_isSilent_boxed_490_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(lean_object* v_msgData_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
uint8_t v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = 0;
v___x_503_ = 0;
v___x_504_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(v_msgData_492_, v___x_502_, v___x_503_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0___boxed(lean_object* v_msgData_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_msgData_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_515_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(uint8_t v___x_520_, lean_object* v_stx_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_filter_x3f_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; 
if (v___x_520_ == 0)
{
lean_object* v___x_570_; 
lean_dec_ref(v___x_525_);
lean_dec_ref(v___x_524_);
lean_dec_ref(v___x_523_);
lean_dec_ref(v___x_522_);
v___x_570_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = l_Lean_Syntax_getArg(v_stx_521_, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
v___x_574_ = l_Lean_Name_mkStr5(v___x_522_, v___x_523_, v___x_524_, v___x_525_, v___x_573_);
lean_inc(v___x_572_);
v___x_575_ = l_Lean_Syntax_isOfKind(v___x_572_, v___x_574_);
lean_dec(v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_572_);
v___x_576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = l_Lean_Syntax_getArg(v___x_572_, v___x_577_);
lean_dec(v___x_572_);
v___x_579_ = l_Lean_Syntax_isNone(v___x_578_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; 
lean_inc(v___x_578_);
v___x_580_ = l_Lean_Syntax_matchesNull(v___x_578_, v___x_571_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec(v___x_578_);
v___x_581_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_581_;
}
else
{
lean_object* v_filter_x3f_582_; lean_object* v___x_583_; 
v_filter_x3f_582_ = l_Lean_Syntax_getArg(v___x_578_, v___x_577_);
lean_dec(v___x_578_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v_filter_x3f_582_);
v_filter_x3f_536_ = v___x_583_;
v___y_537_ = v___y_526_;
v___y_538_ = v___y_527_;
v___y_539_ = v___y_528_;
v___y_540_ = v___y_529_;
v___y_541_ = v___y_530_;
v___y_542_ = v___y_531_;
v___y_543_ = v___y_532_;
v___y_544_ = v___y_533_;
goto v___jp_535_;
}
}
else
{
lean_object* v___x_584_; 
lean_dec(v___x_578_);
v___x_584_ = lean_box(0);
v_filter_x3f_536_ = v___x_584_;
v___y_537_ = v___y_526_;
v___y_538_ = v___y_527_;
v___y_539_ = v___y_528_;
v___y_540_ = v___y_529_;
v___y_541_ = v___y_530_;
v___y_542_ = v___y_531_;
v___y_543_ = v___y_532_;
v___y_544_ = v___y_533_;
goto v___jp_535_;
}
}
}
v___jp_535_:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; uint8_t v___x_547_; lean_object* v___x_548_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = 0;
v___x_548_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_a_546_, v___x_547_, v___y_537_, v___y_538_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
if (lean_obj_tag(v_a_549_) == 1)
{
lean_object* v_val_550_; lean_object* v___x_551_; 
v_val_550_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_a_549_, 1);
v___x_551_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_val_550_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_a_549_);
v___x_552_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1);
v___x_553_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_552_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_553_;
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_a_554_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_548_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_548_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_a_562_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_545_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_545_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed(lean_object* v___x_585_, lean_object* v_stx_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
uint8_t v___x_6874__boxed_600_; lean_object* v_res_601_; 
v___x_6874__boxed_600_ = lean_unbox(v___x_585_);
v_res_601_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(v___x_6874__boxed_600_, v_stx_586_, v___x_587_, v___x_588_, v___x_589_, v___x_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v_stx_586_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(lean_object* v_stx_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___y_629_; lean_object* v___x_630_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
v___x_624_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4));
lean_inc(v_stx_612_);
v___x_627_ = l_Lean_Syntax_isOfKind(v_stx_612_, v___x_626_);
v___x_628_ = lean_box(v___x_627_);
v___y_629_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed), 15, 6);
lean_closure_set(v___y_629_, 0, v___x_628_);
lean_closure_set(v___y_629_, 1, v_stx_612_);
lean_closure_set(v___y_629_, 2, v___x_622_);
lean_closure_set(v___y_629_, 3, v___x_623_);
lean_closure_set(v___y_629_, 4, v___x_624_);
lean_closure_set(v___y_629_, 5, v___x_625_);
v___x_630_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_629_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed(lean_object* v_stx_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(v_stx_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(lean_object* v_00_u03b1_642_, lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v_msg_643_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___boxed(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(v_00_u03b1_654_, v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(lean_object* v_ref_666_, lean_object* v_msgData_667_, uint8_t v_severity_668_, uint8_t v_isSilent_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_666_, v_msgData_667_, v_severity_668_, v_isSilent_669_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_680_, lean_object* v_msgData_681_, lean_object* v_severity_682_, lean_object* v_isSilent_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
uint8_t v_severity_boxed_693_; uint8_t v_isSilent_boxed_694_; lean_object* v_res_695_; 
v_severity_boxed_693_ = lean_unbox(v_severity_682_);
v_isSilent_boxed_694_ = lean_unbox(v_isSilent_683_);
v_res_695_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(v_ref_680_, v_msgData_681_, v_severity_boxed_693_, v_isSilent_boxed_694_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v_ref_680_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1(){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_736_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4));
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14));
v___x_739_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed), 10, 0);
v___x_740_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_736_, v___x_737_, v___x_738_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___boxed(lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(lean_object* v_filter_743_, lean_object* v_as_744_, size_t v_i_745_, size_t v_stop_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_a_752_; uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_eq(v_i_745_, v_stop_746_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_760_; 
v___x_757_ = lean_array_uget_borrowed(v_as_744_, v_i_745_);
lean_inc(v_filter_743_);
lean_inc(v___x_757_);
v___x_760_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v___x_757_, v_filter_743_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; uint8_t v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = lean_unbox(v_a_761_);
lean_dec(v_a_761_);
if (v___x_762_ == 0)
{
v_a_752_ = v_b_747_;
goto v___jp_751_;
}
else
{
uint8_t v___x_763_; 
lean_inc(v___x_757_);
v___x_763_ = l_Lean_Expr_isTrue(v___x_757_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; 
lean_inc(v___x_757_);
v___x_764_ = l_Lean_Expr_isFalse(v___x_757_);
if (v___x_764_ == 0)
{
goto v___jp_758_;
}
else
{
v_a_752_ = v_b_747_;
goto v___jp_751_;
}
}
else
{
v_a_752_ = v_b_747_;
goto v___jp_751_;
}
}
}
else
{
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_765_; uint8_t v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_760_, 1);
v___x_766_ = lean_unbox(v_a_765_);
lean_dec(v_a_765_);
if (v___x_766_ == 0)
{
v_a_752_ = v_b_747_;
goto v___jp_751_;
}
else
{
goto v___jp_758_;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_b_747_);
lean_dec(v_filter_743_);
v_a_767_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_760_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_760_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
v___jp_758_:
{
lean_object* v___x_759_; 
lean_inc(v___x_757_);
v___x_759_ = lean_array_push(v_b_747_, v___x_757_);
v_a_752_ = v___x_759_;
goto v___jp_751_;
}
}
else
{
lean_object* v___x_775_; 
lean_dec(v_filter_743_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_b_747_);
return v___x_775_;
}
v___jp_751_:
{
size_t v___x_753_; size_t v___x_754_; 
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_745_, v___x_753_);
v_i_745_ = v___x_754_;
v_b_747_ = v_a_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg___boxed(lean_object* v_filter_776_, lean_object* v_as_777_, lean_object* v_i_778_, lean_object* v_stop_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
size_t v_i_boxed_784_; size_t v_stop_boxed_785_; lean_object* v_res_786_; 
v_i_boxed_784_ = lean_unbox_usize(v_i_778_);
lean_dec(v_i_778_);
v_stop_boxed_785_ = lean_unbox_usize(v_stop_779_);
lean_dec(v_stop_779_);
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_776_, v_as_777_, v_i_boxed_784_, v_stop_boxed_785_, v_b_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v_as_777_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(lean_object* v_filter_787_, lean_object* v_____do__lift_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_800_ = 0;
v___x_801_ = lean_st_ref_get(v___y_789_);
v___x_802_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_801_, v_____do__lift_788_, v___x_800_);
lean_dec(v___x_801_);
v___x_803_ = lean_array_mk(v___x_802_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v___x_803_);
v___x_806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0));
v___x_807_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v___x_803_);
lean_dec(v_filter_787_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
return v___x_808_;
}
else
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_le(v___x_805_, v___x_805_);
if (v___x_809_ == 0)
{
if (v___x_807_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v___x_803_);
lean_dec(v_filter_787_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_806_);
return v___x_810_;
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_805_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_787_, v___x_803_, v___x_811_, v___x_812_, v___x_806_, v___y_789_, v___y_796_);
lean_dec_ref(v___x_803_);
return v___x_813_;
}
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_805_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_787_, v___x_803_, v___x_814_, v___x_815_, v___x_806_, v___y_789_, v___y_796_);
lean_dec_ref(v___x_803_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed(lean_object* v_filter_817_, lean_object* v_____do__lift_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(v_filter_817_, v_____do__lift_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__1(uint8_t v_isTrue_831_, lean_object* v___f_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
if (v_isTrue_831_ == 0)
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_837_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc(v___y_833_);
v___x_846_ = lean_apply_12(v___f_832_, v_a_845_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
return v___x_846_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref(v___f_832_);
v_a_847_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_844_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_844_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v___y_837_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc(v___y_833_);
v___x_857_ = lean_apply_12(v___f_832_, v_a_856_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
return v___x_857_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___f_832_);
v_a_858_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_855_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_855_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__1___boxed(lean_object* v_isTrue_866_, lean_object* v___f_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_isTrue_boxed_879_; lean_object* v_res_880_; 
v_isTrue_boxed_879_ = lean_unbox(v_isTrue_866_);
v_res_880_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__1(v_isTrue_boxed_879_, v___f_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(lean_object* v_filter_887_, uint8_t v_isTrue_888_, uint8_t v_collapsed_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___f_897_; lean_object* v___x_898_; lean_object* v___y_899_; lean_object* v___x_900_; 
v___f_897_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_897_, 0, v_filter_887_);
v___x_898_ = lean_box(v_isTrue_888_);
v___y_899_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__1___boxed), 13, 2);
lean_closure_set(v___y_899_, 0, v___x_898_);
lean_closure_set(v___y_899_, 1, v___f_897_);
v___x_900_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___y_899_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_925_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_925_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_925_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_925_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_905_ = lean_array_get_size(v_a_901_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_dec_eq(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___y_910_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1));
if (v_isTrue_888_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3));
v___y_910_ = v___x_919_;
goto v___jp_909_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4));
v___y_910_ = v___x_920_;
goto v___jp_909_;
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2));
lean_inc_ref(v___y_910_);
v___x_912_ = lean_string_append(v___y_910_, v___x_911_);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4));
v___x_914_ = l_Lean_Meta_Grind_ppExprArray(v___x_908_, v___x_912_, v_a_901_, v___x_913_, v_collapsed_889_);
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_915_);
v___x_917_ = v___x_903_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_a_901_);
v___x_921_ = lean_box(0);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_921_);
v___x_923_ = v___x_903_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_900_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_900_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___boxed(lean_object* v_filter_934_, lean_object* v_isTrue_935_, lean_object* v_collapsed_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_isTrue_boxed_944_; uint8_t v_collapsed_boxed_945_; lean_object* v_res_946_; 
v_isTrue_boxed_944_ = lean_unbox(v_isTrue_935_);
v_collapsed_boxed_945_ = lean_unbox(v_collapsed_936_);
v_res_946_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_filter_934_, v_isTrue_boxed_944_, v_collapsed_boxed_945_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(lean_object* v_filter_947_, uint8_t v_isTrue_948_, uint8_t v_collapsed_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_filter_947_, v_isTrue_948_, v_collapsed_949_, v_a_950_, v_a_951_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___boxed(lean_object* v_filter_960_, lean_object* v_isTrue_961_, lean_object* v_collapsed_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
uint8_t v_isTrue_boxed_972_; uint8_t v_collapsed_boxed_973_; lean_object* v_res_974_; 
v_isTrue_boxed_972_ = lean_unbox(v_isTrue_961_);
v_collapsed_boxed_973_ = lean_unbox(v_collapsed_962_);
v_res_974_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(v_filter_960_, v_isTrue_boxed_972_, v_collapsed_boxed_973_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(lean_object* v_filter_975_, lean_object* v_as_976_, size_t v_i_977_, size_t v_stop_978_, lean_object* v_b_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_975_, v_as_976_, v_i_977_, v_stop_978_, v_b_979_, v___y_980_, v___y_987_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___boxed(lean_object* v_filter_992_, lean_object* v_as_993_, lean_object* v_i_994_, lean_object* v_stop_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
size_t v_i_boxed_1008_; size_t v_stop_boxed_1009_; lean_object* v_res_1010_; 
v_i_boxed_1008_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_stop_boxed_1009_ = lean_unbox_usize(v_stop_995_);
lean_dec(v_stop_995_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(v_filter_992_, v_as_993_, v_i_boxed_1008_, v_stop_boxed_1009_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v_as_993_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(lean_object* v_filter_x3f_1014_, uint8_t v_isTrue_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = 0;
v___x_1028_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_a_1026_, v_isTrue_1015_, v___x_1027_, v___y_1016_, v___y_1017_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
if (lean_obj_tag(v_a_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
v_val_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v_a_1029_, 1);
v___x_1031_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_val_1030_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; lean_object* v___y_1034_; 
lean_dec(v_a_1029_);
v___x_1032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0));
if (v_isTrue_1015_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1));
v___y_1034_ = v___x_1041_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2));
v___y_1034_ = v___x_1042_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1035_ = lean_string_append(v___x_1032_, v___y_1034_);
v___x_1036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
v___x_1039_ = l_Lean_MessageData_ofFormat(v___x_1038_);
v___x_1040_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_1039_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1040_;
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1028_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1028_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1025_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1025_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed(lean_object* v_filter_x3f_1059_, lean_object* v_isTrue_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v_isTrue_boxed_1070_; lean_object* v_res_1071_; 
v_isTrue_boxed_1070_ = lean_unbox(v_isTrue_1060_);
v_res_1071_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(v_filter_x3f_1059_, v_isTrue_boxed_1070_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(lean_object* v_filter_x3f_1072_, uint8_t v_isTrue_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_box(v_isTrue_1073_);
v___f_1084_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1084_, 0, v_filter_x3f_1072_);
lean_closure_set(v___f_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1084_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___boxed(lean_object* v_filter_x3f_1086_, lean_object* v_isTrue_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
uint8_t v_isTrue_boxed_1097_; lean_object* v_res_1098_; 
v_isTrue_boxed_1097_ = lean_unbox(v_isTrue_1087_);
v_res_1098_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v_filter_x3f_1086_, v_isTrue_boxed_1097_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(lean_object* v_stx_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1));
lean_inc(v_stx_1112_);
v___x_1123_ = l_Lean_Syntax_isOfKind(v_stx_1112_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_stx_1112_);
v___x_1124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = l_Lean_Syntax_getArg(v_stx_1112_, v___x_1125_);
lean_dec(v_stx_1112_);
v___x_1127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2));
lean_inc(v___x_1126_);
v___x_1128_ = l_Lean_Syntax_isOfKind(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec(v___x_1126_);
v___x_1129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = l_Lean_Syntax_getArg(v___x_1126_, v___x_1130_);
lean_dec(v___x_1126_);
v___x_1132_ = l_Lean_Syntax_isNone(v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
lean_inc(v___x_1131_);
v___x_1133_ = l_Lean_Syntax_matchesNull(v___x_1131_, v___x_1125_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1131_);
v___x_1134_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1134_;
}
else
{
lean_object* v_filter_x3f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_filter_x3f_1135_ = l_Lean_Syntax_getArg(v___x_1131_, v___x_1130_);
lean_dec(v___x_1131_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_filter_x3f_1135_);
v___x_1137_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v___x_1136_, v___x_1128_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
return v___x_1137_;
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v___x_1131_);
v___x_1138_ = lean_box(0);
v___x_1139_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v___x_1138_, v___x_1128_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed(lean_object* v_stx_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(v_stx_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1(){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1));
v___x_1158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1));
v___x_1159_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed), 10, 0);
v___x_1160_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1156_, v___x_1157_, v___x_1158_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___boxed(lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(lean_object* v_stx_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_filter_x3f_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1));
lean_inc(v_stx_1170_);
v___x_1193_ = l_Lean_Syntax_isOfKind(v_stx_1170_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_stx_1170_);
v___x_1194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = l_Lean_Syntax_getArg(v_stx_1170_, v___x_1195_);
lean_dec(v_stx_1170_);
v___x_1197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2));
lean_inc(v___x_1196_);
v___x_1198_ = l_Lean_Syntax_isOfKind(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v___x_1196_);
v___x_1199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l_Lean_Syntax_getArg(v___x_1196_, v___x_1200_);
lean_dec(v___x_1196_);
v___x_1202_ = l_Lean_Syntax_isNone(v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
lean_inc(v___x_1201_);
v___x_1203_ = l_Lean_Syntax_matchesNull(v___x_1201_, v___x_1195_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
lean_dec(v___x_1201_);
v___x_1204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1204_;
}
else
{
lean_object* v_filter_x3f_1205_; lean_object* v___x_1206_; 
v_filter_x3f_1205_ = l_Lean_Syntax_getArg(v___x_1201_, v___x_1200_);
lean_dec(v___x_1201_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_filter_x3f_1205_);
v_filter_x3f_1181_ = v___x_1206_;
v___y_1182_ = v_a_1171_;
v___y_1183_ = v_a_1172_;
v___y_1184_ = v_a_1173_;
v___y_1185_ = v_a_1174_;
v___y_1186_ = v_a_1175_;
v___y_1187_ = v_a_1176_;
v___y_1188_ = v_a_1177_;
v___y_1189_ = v_a_1178_;
goto v___jp_1180_;
}
}
else
{
lean_object* v___x_1207_; 
lean_dec(v___x_1201_);
v___x_1207_ = lean_box(0);
v_filter_x3f_1181_ = v___x_1207_;
v___y_1182_ = v_a_1171_;
v___y_1183_ = v_a_1172_;
v___y_1184_ = v_a_1173_;
v___y_1185_ = v_a_1174_;
v___y_1186_ = v_a_1175_;
v___y_1187_ = v_a_1176_;
v___y_1188_ = v_a_1177_;
v___y_1189_ = v_a_1178_;
goto v___jp_1180_;
}
}
}
v___jp_1180_:
{
uint8_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = 0;
v___x_1191_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v_filter_x3f_1181_, v___x_1190_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed(lean_object* v_stx_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(v_stx_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1(){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1224_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1));
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1));
v___x_1227_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed), 10, 0);
v___x_1228_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1224_, v___x_1225_, v___x_1226_, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___boxed(lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(lean_object* v_filter_1231_, lean_object* v_x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_filter_1231_);
v___x_1236_ = 0;
v___x_1237_ = lean_box(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v_head_1239_; lean_object* v_tail_1240_; lean_object* v___x_1241_; 
v_head_1239_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_head_1239_);
v_tail_1240_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_tail_1240_);
lean_dec_ref_known(v_x_1232_, 2);
lean_inc(v_filter_1231_);
v___x_1241_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_head_1239_, v_filter_1231_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
v___x_1243_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
if (v___x_1243_ == 0)
{
lean_dec_ref_known(v___x_1241_, 1);
v_x_1232_ = v_tail_1240_;
goto _start;
}
else
{
lean_dec(v_tail_1240_);
lean_dec(v_filter_1231_);
return v___x_1241_;
}
}
else
{
lean_dec(v_tail_1240_);
lean_dec(v_filter_1231_);
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___boxed(lean_object* v_filter_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(v_filter_1245_, v_x_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec(v___y_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; uint8_t v___x_1255_; 
v_head_1253_ = lean_ctor_get(v_x_1251_, 0);
lean_inc_n(v_head_1253_, 2);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 1);
lean_inc(v_tail_1254_);
lean_dec_ref_known(v_x_1251_, 2);
v___x_1255_ = l_Lean_Expr_isFalse(v_head_1253_);
if (v___x_1255_ == 0)
{
lean_dec(v_head_1253_);
v_x_1251_ = v_tail_1254_;
goto _start;
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_tail_1254_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_head_1253_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_box(0);
return v___x_1259_;
}
else
{
lean_object* v_head_1260_; lean_object* v_tail_1261_; uint8_t v___x_1262_; 
v_head_1260_ = lean_ctor_get(v_x_1258_, 0);
lean_inc_n(v_head_1260_, 2);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 1);
lean_inc(v_tail_1261_);
lean_dec_ref_known(v_x_1258_, 2);
v___x_1262_ = l_Lean_Expr_isTrue(v_head_1260_);
if (v___x_1262_ == 0)
{
lean_dec(v_head_1260_);
v_x_1258_ = v_tail_1261_;
goto _start;
}
else
{
lean_object* v___x_1264_; 
lean_dec(v_tail_1261_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_head_1260_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_x_1266_);
return v___x_1272_;
}
else
{
lean_object* v_head_1273_; lean_object* v_tail_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1294_; 
v_head_1273_ = lean_ctor_get(v_x_1265_, 0);
v_tail_1274_ = lean_ctor_get(v_x_1265_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1276_ = v_x_1265_;
v_isShared_1277_ = v_isSharedCheck_1294_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_tail_1274_);
lean_inc(v_head_1273_);
lean_dec(v_x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1294_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
lean_inc(v_head_1273_);
v___x_1278_ = l_Lean_Meta_Grind_isSupportApp(v_head_1273_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; uint8_t v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
if (v___x_1280_ == 0)
{
lean_del_object(v___x_1276_);
lean_dec(v_head_1273_);
v_x_1265_ = v_tail_1274_;
goto _start;
}
else
{
lean_object* v___x_1283_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_x_1266_);
v___x_1283_ = v___x_1276_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_head_1273_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_x_1266_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v_x_1265_ = v_tail_1274_;
v_x_1266_ = v___x_1283_;
goto _start;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_del_object(v___x_1276_);
lean_dec(v_tail_1274_);
lean_dec(v_head_1273_);
lean_dec(v_x_1266_);
v_a_1286_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1278_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1278_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg___boxed(lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(v_x_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(uint8_t v_a_1303_, uint8_t v_a_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
if (lean_obj_tag(v_x_1305_) == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_x_1306_);
return v___x_1312_;
}
else
{
lean_object* v_head_1313_; lean_object* v_tail_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1338_; 
v_head_1313_ = lean_ctor_get(v_x_1305_, 0);
v_tail_1314_ = lean_ctor_get(v_x_1305_, 1);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1316_ = v_x_1305_;
v_isShared_1317_ = v_isSharedCheck_1338_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_tail_1314_);
lean_inc(v_head_1313_);
lean_dec(v_x_1305_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1338_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
uint8_t v_a_1319_; lean_object* v___x_1325_; 
lean_inc(v_head_1313_);
v___x_1325_ = l_Lean_Meta_Grind_isSupportApp(v_head_1313_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; uint8_t v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_unbox(v_a_1326_);
lean_dec(v_a_1326_);
if (v___x_1327_ == 0)
{
v_a_1319_ = v_a_1303_;
goto v___jp_1318_;
}
else
{
v_a_1319_ = v_a_1304_;
goto v___jp_1318_;
}
}
else
{
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1328_; uint8_t v___x_1329_; 
v_a_1328_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1329_ = lean_unbox(v_a_1328_);
lean_dec(v_a_1328_);
v_a_1319_ = v___x_1329_;
goto v___jp_1318_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_del_object(v___x_1316_);
lean_dec(v_tail_1314_);
lean_dec(v_head_1313_);
lean_dec(v_x_1306_);
v_a_1330_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1325_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
v___jp_1318_:
{
if (v_a_1319_ == 0)
{
lean_del_object(v___x_1316_);
lean_dec(v_head_1313_);
v_x_1305_ = v_tail_1314_;
goto _start;
}
else
{
lean_object* v___x_1322_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v_x_1306_);
v___x_1322_ = v___x_1316_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_head_1313_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_x_1306_);
v___x_1322_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v_x_1305_ = v_tail_1314_;
v_x_1306_ = v___x_1322_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg___boxed(lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_a_22878__boxed_1348_; uint8_t v_a_22879__boxed_1349_; lean_object* v_res_1350_; 
v_a_22878__boxed_1348_ = lean_unbox(v_a_1339_);
v_a_22879__boxed_1349_ = lean_unbox(v_a_1340_);
v_res_1350_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(v_a_22878__boxed_1348_, v_a_22879__boxed_1349_, v_x_1341_, v_x_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(lean_object* v_filter_1353_, lean_object* v_as_x27_1354_, lean_object* v_b_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
if (lean_obj_tag(v_as_x27_1354_) == 0)
{
lean_object* v___x_1367_; 
lean_dec(v_filter_1353_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_b_1355_);
return v___x_1367_;
}
else
{
lean_object* v_head_1368_; lean_object* v_tail_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1468_; 
v_head_1368_ = lean_ctor_get(v_as_x27_1354_, 0);
v_tail_1369_ = lean_ctor_get(v_as_x27_1354_, 1);
v_fst_1370_ = lean_ctor_get(v_b_1355_, 0);
v_snd_1371_ = lean_ctor_get(v_b_1355_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_b_1355_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1373_ = v_b_1355_;
v_isShared_1374_ = v_isSharedCheck_1468_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_b_1355_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1468_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1380_; 
lean_inc(v_head_1368_);
v___x_1380_ = l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(v_head_1368_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; 
lean_inc(v_head_1368_);
v___x_1381_ = l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(v_head_1368_);
if (lean_obj_tag(v___x_1381_) == 0)
{
if (lean_obj_tag(v_head_1368_) == 1)
{
lean_object* v_tail_1382_; 
v_tail_1382_ = lean_ctor_get(v_head_1368_, 1);
if (lean_obj_tag(v_tail_1382_) == 1)
{
lean_object* v_head_1383_; lean_object* v_regularEqcs_1384_; lean_object* v___y_1386_; lean_object* v_a_1387_; lean_object* v_a_1402_; lean_object* v___x_1423_; 
lean_del_object(v___x_1373_);
v_head_1383_ = lean_ctor_get(v_head_1368_, 0);
v_regularEqcs_1384_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0));
lean_inc(v_head_1383_);
v___x_1423_ = l_Lean_Meta_isProof(v_head_1383_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; uint8_t v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_unbox(v_a_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_inc_ref(v_head_1368_);
lean_inc(v_filter_1353_);
v___x_1426_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(v_filter_1353_, v_head_1368_, v___y_1356_, v___y_1363_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; uint8_t v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = lean_unbox(v_a_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_a_1427_);
lean_dec(v_a_1424_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_fst_1370_);
lean_ctor_set(v___x_1429_, 1, v_snd_1371_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1429_;
goto _start;
}
else
{
lean_object* v___x_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_unbox(v_a_1427_);
lean_dec(v_a_1427_);
v___x_1433_ = lean_unbox(v_a_1424_);
lean_dec(v_a_1424_);
lean_inc_ref(v_head_1368_);
v___x_1434_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(v___x_1432_, v___x_1433_, v_head_1368_, v___x_1431_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = l_List_reverse___redArg(v_a_1435_);
v_a_1402_ = v___x_1436_;
goto v___jp_1401_;
}
else
{
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1437_; 
v_a_1437_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1434_, 1);
v_a_1402_ = v_a_1437_;
goto v___jp_1401_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec(v_filter_1353_);
v_a_1438_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1434_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1434_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1424_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec(v_filter_1353_);
v_a_1446_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1426_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1426_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_a_1424_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_fst_1370_);
lean_ctor_set(v___x_1454_, 1, v_snd_1371_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1454_;
goto _start;
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec(v_filter_1353_);
v_a_1456_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1423_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1423_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
v___jp_1385_:
{
uint8_t v___x_1388_; 
v___x_1388_ = l_List_isEmpty___redArg(v_a_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1389_ = l_Lean_Meta_Grind_ppEqc(v_a_1387_, v_regularEqcs_1384_);
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = lean_mk_empty_array_with_capacity(v___x_1390_);
v___x_1392_ = lean_array_push(v___x_1391_, v___x_1389_);
v___x_1393_ = l_Lean_Meta_Grind_ppEqc(v___y_1386_, v___x_1392_);
v___x_1394_ = lean_array_push(v_fst_1370_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v_snd_1371_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1395_;
goto _start;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_a_1387_);
v___x_1397_ = l_Lean_Meta_Grind_ppEqc(v___y_1386_, v_regularEqcs_1384_);
v___x_1398_ = lean_array_push(v_fst_1370_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_snd_1371_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1399_;
goto _start;
}
}
v___jp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = l_List_lengthTR___redArg(v_a_1402_);
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_nat_dec_le(v___x_1403_, v___x_1404_);
lean_dec(v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_box(0);
lean_inc_ref(v_head_1368_);
v___x_1407_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(v_head_1368_, v___x_1406_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = l_List_reverse___redArg(v_a_1408_);
v___y_1386_ = v_a_1402_;
v_a_1387_ = v___x_1409_;
goto v___jp_1385_;
}
else
{
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1407_, 1);
v___y_1386_ = v_a_1402_;
v_a_1387_ = v_a_1410_;
goto v___jp_1385_;
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_a_1402_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
lean_dec(v_filter_1353_);
v_a_1411_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1407_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1407_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec(v_a_1402_);
lean_inc_ref(v_head_1368_);
v___x_1419_ = l_Lean_Meta_Grind_ppEqc(v_head_1368_, v_regularEqcs_1384_);
v___x_1420_ = lean_array_push(v_snd_1371_, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_fst_1370_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1421_;
goto _start;
}
}
}
else
{
goto v___jp_1375_;
}
}
else
{
goto v___jp_1375_;
}
}
else
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1381_, 1);
lean_del_object(v___x_1373_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_fst_1370_);
lean_ctor_set(v___x_1464_, 1, v_snd_1371_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1464_;
goto _start;
}
}
else
{
lean_object* v___x_1466_; 
lean_dec_ref_known(v___x_1380_, 1);
lean_del_object(v___x_1373_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_fst_1370_);
lean_ctor_set(v___x_1466_, 1, v_snd_1371_);
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1466_;
goto _start;
}
v___jp_1375_:
{
lean_object* v___x_1377_; 
if (v_isShared_1374_ == 0)
{
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_fst_1370_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_snd_1371_);
v___x_1377_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v_as_x27_1354_ = v_tail_1369_;
v_b_1355_ = v___x_1377_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___boxed(lean_object* v_filter_1469_, lean_object* v_as_x27_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(v_filter_1469_, v_as_x27_1470_, v_b_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec(v_as_x27_1470_);
return v_res_1483_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3));
v___x_1491_ = l_Lean_MessageData_ofFormat(v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6));
v___x_1496_ = l_Lean_MessageData_ofFormat(v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(lean_object* v___x_1497_, uint8_t v_collapsed_1498_, lean_object* v_regularEqcs_1499_, lean_object* v_filter_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_regularEqcs_1513_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1527_ = lean_st_ref_get(v___y_1501_);
v___x_1528_ = 1;
v___x_1529_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_1527_, v___x_1528_);
lean_dec(v___x_1527_);
lean_inc_ref(v_regularEqcs_1499_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_regularEqcs_1499_);
lean_ctor_set(v___x_1530_, 1, v_regularEqcs_1499_);
v___x_1531_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(v_filter_1500_, v___x_1529_, v___x_1530_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___x_1529_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_fst_1533_; lean_object* v_snd_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_fst_1533_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_fst_1533_);
v_snd_1534_ = lean_ctor_get(v_a_1532_, 1);
lean_inc(v_snd_1534_);
lean_dec(v_a_1532_);
v___x_1535_ = lean_array_get_size(v_snd_1534_);
v___x_1536_ = lean_nat_dec_eq(v___x_1535_, v___x_1497_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; double v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1));
v___x_1538_ = lean_box(0);
lean_inc(v___x_1497_);
v___x_1539_ = lean_float_of_nat(v___x_1497_);
v___x_1540_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1541_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1541_, 0, v___x_1537_);
lean_ctor_set(v___x_1541_, 1, v___x_1538_);
lean_ctor_set(v___x_1541_, 2, v___x_1540_);
lean_ctor_set_float(v___x_1541_, sizeof(void*)*3, v___x_1539_);
lean_ctor_set_float(v___x_1541_, sizeof(void*)*3 + 8, v___x_1539_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*3 + 16, v___x_1528_);
v___x_1542_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7);
v___x_1543_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
lean_ctor_set(v___x_1543_, 2, v_snd_1534_);
v___x_1544_ = lean_array_push(v_fst_1533_, v___x_1543_);
v_regularEqcs_1513_ = v___x_1544_;
goto v___jp_1512_;
}
else
{
lean_dec(v_snd_1534_);
v_regularEqcs_1513_ = v_fst_1533_;
goto v___jp_1512_;
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v___x_1497_);
v_a_1545_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1531_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1531_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_array_get_size(v_regularEqcs_1513_);
v___x_1515_ = lean_nat_dec_eq(v___x_1514_, v___x_1497_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; double v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1));
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_float_of_nat(v___x_1497_);
v___x_1519_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1520_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1520_, 0, v___x_1516_);
lean_ctor_set(v___x_1520_, 1, v___x_1517_);
lean_ctor_set(v___x_1520_, 2, v___x_1519_);
lean_ctor_set_float(v___x_1520_, sizeof(void*)*3, v___x_1518_);
lean_ctor_set_float(v___x_1520_, sizeof(void*)*3 + 8, v___x_1518_);
lean_ctor_set_uint8(v___x_1520_, sizeof(void*)*3 + 16, v_collapsed_1498_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4);
v___x_1522_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_ctor_set(v___x_1522_, 2, v_regularEqcs_1513_);
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v_regularEqcs_1513_);
lean_dec(v___x_1497_);
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed(lean_object* v___x_1553_, lean_object* v_collapsed_1554_, lean_object* v_regularEqcs_1555_, lean_object* v_filter_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_collapsed_boxed_1568_; lean_object* v_res_1569_; 
v_collapsed_boxed_1568_ = lean_unbox(v_collapsed_1554_);
v_res_1569_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(v___x_1553_, v_collapsed_boxed_1568_, v_regularEqcs_1555_, v_filter_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(lean_object* v_filter_1570_, uint8_t v_collapsed_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v_regularEqcs_1580_; lean_object* v___x_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v_regularEqcs_1580_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0));
v___x_1581_ = lean_box(v_collapsed_1571_);
v___f_1582_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed), 15, 4);
lean_closure_set(v___f_1582_, 0, v___x_1579_);
lean_closure_set(v___f_1582_, 1, v___x_1581_);
lean_closure_set(v___f_1582_, 2, v_regularEqcs_1580_);
lean_closure_set(v___f_1582_, 3, v_filter_1570_);
v___x_1583_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_1582_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___boxed(lean_object* v_filter_1584_, lean_object* v_collapsed_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
uint8_t v_collapsed_boxed_1593_; lean_object* v_res_1594_; 
v_collapsed_boxed_1593_ = lean_unbox(v_collapsed_1585_);
v_res_1594_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(v_filter_1584_, v_collapsed_boxed_1593_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(lean_object* v_filter_1595_, uint8_t v_collapsed_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(v_filter_1595_, v_collapsed_1596_, v_a_1597_, v_a_1598_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___boxed(lean_object* v_filter_1607_, lean_object* v_collapsed_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
uint8_t v_collapsed_boxed_1618_; lean_object* v_res_1619_; 
v_collapsed_boxed_1618_ = lean_unbox(v_collapsed_1608_);
v_res_1619_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(v_filter_1607_, v_collapsed_boxed_1618_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(v_x_1620_, v_x_1621_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___boxed(lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(v_x_1634_, v_x_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec(v___y_1636_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(lean_object* v_filter_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(v_filter_1648_, v_x_1649_, v___y_1650_, v___y_1657_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___boxed(lean_object* v_filter_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(v_filter_1662_, v_x_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4(uint8_t v_a_1676_, uint8_t v_a_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(v_a_1676_, v_a_1677_, v_x_1678_, v_x_1679_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___boxed(lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v_a_23449__boxed_1707_; uint8_t v_a_23450__boxed_1708_; lean_object* v_res_1709_; 
v_a_23449__boxed_1707_ = lean_unbox(v_a_1692_);
v_a_23450__boxed_1708_ = lean_unbox(v_a_1693_);
v_res_1709_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4(v_a_23449__boxed_1707_, v_a_23450__boxed_1708_, v_x_1694_, v_x_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5(lean_object* v_filter_1710_, lean_object* v_as_1711_, lean_object* v_as_x27_1712_, lean_object* v_b_1713_, lean_object* v_a_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(v_filter_1710_, v_as_x27_1712_, v_b_1713_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___boxed(lean_object* v_filter_1727_, lean_object* v_as_1728_, lean_object* v_as_x27_1729_, lean_object* v_b_1730_, lean_object* v_a_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5(v_filter_1727_, v_as_1728_, v_as_x27_1729_, v_b_1730_, v_a_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec(v_as_x27_1729_);
lean_dec(v_as_1728_);
return v_res_1743_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0));
v___x_1746_ = l_Lean_stringToMessageData(v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(uint8_t v___x_1747_, lean_object* v_stx_1748_, lean_object* v___x_1749_, lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_filter_x3f_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; 
if (v___x_1747_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v___x_1752_);
lean_dec_ref(v___x_1751_);
lean_dec_ref(v___x_1750_);
lean_dec_ref(v___x_1749_);
v___x_1797_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = l_Lean_Syntax_getArg(v_stx_1748_, v___x_1798_);
v___x_1800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
v___x_1801_ = l_Lean_Name_mkStr5(v___x_1749_, v___x_1750_, v___x_1751_, v___x_1752_, v___x_1800_);
lean_inc(v___x_1799_);
v___x_1802_ = l_Lean_Syntax_isOfKind(v___x_1799_, v___x_1801_);
lean_dec(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_dec(v___x_1799_);
v___x_1803_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = l_Lean_Syntax_getArg(v___x_1799_, v___x_1804_);
lean_dec(v___x_1799_);
v___x_1806_ = l_Lean_Syntax_isNone(v___x_1805_);
if (v___x_1806_ == 0)
{
uint8_t v___x_1807_; 
lean_inc(v___x_1805_);
v___x_1807_ = l_Lean_Syntax_matchesNull(v___x_1805_, v___x_1798_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; 
lean_dec(v___x_1805_);
v___x_1808_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_1808_;
}
else
{
lean_object* v_filter_x3f_1809_; lean_object* v___x_1810_; 
v_filter_x3f_1809_ = l_Lean_Syntax_getArg(v___x_1805_, v___x_1804_);
lean_dec(v___x_1805_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_filter_x3f_1809_);
v_filter_x3f_1763_ = v___x_1810_;
v___y_1764_ = v___y_1753_;
v___y_1765_ = v___y_1754_;
v___y_1766_ = v___y_1755_;
v___y_1767_ = v___y_1756_;
v___y_1768_ = v___y_1757_;
v___y_1769_ = v___y_1758_;
v___y_1770_ = v___y_1759_;
v___y_1771_ = v___y_1760_;
goto v___jp_1762_;
}
}
else
{
lean_object* v___x_1811_; 
lean_dec(v___x_1805_);
v___x_1811_ = lean_box(0);
v_filter_x3f_1763_ = v___x_1811_;
v___y_1764_ = v___y_1753_;
v___y_1765_ = v___y_1754_;
v___y_1766_ = v___y_1755_;
v___y_1767_ = v___y_1756_;
v___y_1768_ = v___y_1757_;
v___y_1769_ = v___y_1758_;
v___y_1770_ = v___y_1759_;
v___y_1771_ = v___y_1760_;
goto v___jp_1762_;
}
}
}
v___jp_1762_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = 0;
v___x_1775_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(v_a_1773_, v___x_1774_, v___y_1764_, v___y_1765_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
if (lean_obj_tag(v_a_1776_) == 1)
{
lean_object* v_val_1777_; lean_object* v___x_1778_; 
v_val_1777_ = lean_ctor_get(v_a_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v_a_1776_, 1);
v___x_1778_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_val_1777_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_a_1776_);
v___x_1779_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1);
v___x_1780_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_1779_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1780_;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1775_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1775_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1772_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1772_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed(lean_object* v___x_1812_, lean_object* v_stx_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v___x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v___x_483__boxed_1827_; lean_object* v_res_1828_; 
v___x_483__boxed_1827_ = lean_unbox(v___x_1812_);
v_res_1828_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(v___x_483__boxed_1827_, v_stx_1813_, v___x_1814_, v___x_1815_, v___x_1816_, v___x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v_stx_1813_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(lean_object* v_stx_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___y_1853_; lean_object* v___x_1854_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
v___x_1847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
v___x_1848_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_1849_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
v___x_1850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1));
lean_inc(v_stx_1836_);
v___x_1851_ = l_Lean_Syntax_isOfKind(v_stx_1836_, v___x_1850_);
v___x_1852_ = lean_box(v___x_1851_);
v___y_1853_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1853_, 0, v___x_1852_);
lean_closure_set(v___y_1853_, 1, v_stx_1836_);
lean_closure_set(v___y_1853_, 2, v___x_1846_);
lean_closure_set(v___y_1853_, 3, v___x_1847_);
lean_closure_set(v___y_1853_, 4, v___x_1848_);
lean_closure_set(v___y_1853_, 5, v___x_1849_);
v___x_1854_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_1853_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed(lean_object* v_stx_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(v_stx_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1(){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1871_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1));
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1));
v___x_1874_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed), 10, 0);
v___x_1875_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1871_, v___x_1872_, v___x_1873_, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___boxed(lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(lean_object* v_msgs_1878_, lean_object* v_msg_x3f_1879_){
_start:
{
if (lean_obj_tag(v_msg_x3f_1879_) == 1)
{
lean_object* v_val_1880_; lean_object* v___x_1881_; 
v_val_1880_ = lean_ctor_get(v_msg_x3f_1879_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v_msg_x3f_1879_, 1);
v___x_1881_ = lean_array_push(v_msgs_1878_, v_val_1880_);
return v___x_1881_;
}
else
{
lean_dec(v_msg_x3f_1879_);
return v_msgs_1878_;
}
}
}
static double _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2(void){
_start:
{
lean_object* v___x_1885_; double v___x_1886_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_float_of_nat(v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3(void){
_start:
{
lean_object* v___x_1887_; uint8_t v___x_1888_; double v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1887_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1888_ = 0;
v___x_1889_ = lean_float_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2);
v___x_1890_ = lean_box(0);
v___x_1891_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1));
v___x_1892_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1890_);
lean_ctor_set(v___x_1892_, 2, v___x_1887_);
lean_ctor_set_float(v___x_1892_, sizeof(void*)*3, v___x_1889_);
lean_ctor_set_float(v___x_1892_, sizeof(void*)*3 + 8, v___x_1889_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 16, v___x_1888_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5));
v___x_1897_ = l_Lean_MessageData_ofFormat(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg(lean_object* v_filter_1898_, uint8_t v_isSilent_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_msgs_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; 
v_msgs_1907_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0));
v___x_1908_ = 1;
lean_inc(v_filter_1898_);
v___x_1909_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_filter_1898_, v___x_1908_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v_msgs_1907_, v_a_1910_);
v___x_1912_ = 0;
lean_inc(v_filter_1898_);
v___x_1913_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_filter_1898_, v___x_1908_, v___x_1912_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v___x_1911_, v_a_1914_);
lean_inc(v_filter_1898_);
v___x_1916_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_filter_1898_, v___x_1912_, v___x_1912_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v___x_1915_, v_a_1917_);
v___x_1919_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(v_filter_1898_, v___x_1912_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_ref_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_ref_1921_ = lean_ctor_get(v_a_1904_, 2);
v___x_1922_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v___x_1918_, v_a_1920_);
v___x_1923_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3);
v___x_1924_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6);
v___x_1925_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
lean_ctor_set(v___x_1925_, 2, v___x_1922_);
v___x_1926_ = 0;
v___x_1927_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_1921_, v___x_1925_, v___x_1926_, v_isSilent_1899_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
return v___x_1927_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v___x_1918_);
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v___x_1915_);
lean_dec(v_filter_1898_);
v_a_1936_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1916_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1916_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v___x_1911_);
lean_dec(v_filter_1898_);
v_a_1944_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1913_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1913_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_filter_1898_);
v_a_1952_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1909_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1909_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___redArg___boxed(lean_object* v_filter_1960_, lean_object* v_isSilent_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
uint8_t v_isSilent_boxed_1969_; lean_object* v_res_1970_; 
v_isSilent_boxed_1969_ = lean_unbox(v_isSilent_1961_);
v_res_1970_ = l_Lean_Elab_Tactic_Grind_showState___redArg(v_filter_1960_, v_isSilent_boxed_1969_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState(lean_object* v_filter_1971_, uint8_t v_isSilent_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Elab_Tactic_Grind_showState___redArg(v_filter_1971_, v_isSilent_1972_, v_a_1973_, v_a_1974_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_showState___boxed(lean_object* v_filter_1983_, lean_object* v_isSilent_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
uint8_t v_isSilent_boxed_1994_; lean_object* v_res_1995_; 
v_isSilent_boxed_1994_ = lean_unbox(v_isSilent_1984_);
v_res_1995_ = l_Lean_Elab_Tactic_Grind_showState(v_filter_1983_, v_isSilent_boxed_1994_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(uint8_t v___x_1996_, lean_object* v_stx_1997_, lean_object* v___x_1998_, lean_object* v___x_1999_, lean_object* v___x_2000_, lean_object* v___x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_filter_x3f_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; 
if (v___x_1996_ == 0)
{
lean_object* v___x_2033_; 
lean_dec_ref(v___x_2001_);
lean_dec_ref(v___x_2000_);
lean_dec_ref(v___x_1999_);
lean_dec_ref(v___x_1998_);
v___x_2033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = l_Lean_Syntax_getArg(v_stx_1997_, v___x_2034_);
v___x_2036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
v___x_2037_ = l_Lean_Name_mkStr5(v___x_1998_, v___x_1999_, v___x_2000_, v___x_2001_, v___x_2036_);
lean_inc(v___x_2035_);
v___x_2038_ = l_Lean_Syntax_isOfKind(v___x_2035_, v___x_2037_);
lean_dec(v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec(v___x_2035_);
v___x_2039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = l_Lean_Syntax_getArg(v___x_2035_, v___x_2040_);
lean_dec(v___x_2035_);
v___x_2042_ = l_Lean_Syntax_isNone(v___x_2041_);
if (v___x_2042_ == 0)
{
uint8_t v___x_2043_; 
lean_inc(v___x_2041_);
v___x_2043_ = l_Lean_Syntax_matchesNull(v___x_2041_, v___x_2034_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_dec(v___x_2041_);
v___x_2044_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_2044_;
}
else
{
lean_object* v_filter_x3f_2045_; lean_object* v___x_2046_; 
v_filter_x3f_2045_ = l_Lean_Syntax_getArg(v___x_2041_, v___x_2040_);
lean_dec(v___x_2041_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_filter_x3f_2045_);
v_filter_x3f_2012_ = v___x_2046_;
v___y_2013_ = v___y_2002_;
v___y_2014_ = v___y_2003_;
v___y_2015_ = v___y_2004_;
v___y_2016_ = v___y_2005_;
v___y_2017_ = v___y_2006_;
v___y_2018_ = v___y_2007_;
v___y_2019_ = v___y_2008_;
v___y_2020_ = v___y_2009_;
goto v___jp_2011_;
}
}
else
{
lean_object* v___x_2047_; 
lean_dec(v___x_2041_);
v___x_2047_ = lean_box(0);
v_filter_x3f_2012_ = v___x_2047_;
v___y_2013_ = v___y_2002_;
v___y_2014_ = v___y_2003_;
v___y_2015_ = v___y_2004_;
v___y_2016_ = v___y_2005_;
v___y_2017_ = v___y_2006_;
v___y_2018_ = v___y_2007_;
v___y_2019_ = v___y_2008_;
v___y_2020_ = v___y_2009_;
goto v___jp_2011_;
}
}
}
v___jp_2011_:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = 0;
v___x_2024_ = l_Lean_Elab_Tactic_Grind_showState___redArg(v_a_2022_, v___x_2023_, v___y_2013_, v___y_2014_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2024_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2021_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2021_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed(lean_object* v___x_2048_, lean_object* v_stx_2049_, lean_object* v___x_2050_, lean_object* v___x_2051_, lean_object* v___x_2052_, lean_object* v___x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v___x_274__boxed_2063_; lean_object* v_res_2064_; 
v___x_274__boxed_2063_ = lean_unbox(v___x_2048_);
v_res_2064_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(v___x_274__boxed_2063_, v_stx_2049_, v___x_2050_, v___x_2051_, v___x_2052_, v___x_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_stx_2049_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(lean_object* v_stx_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___y_2089_; lean_object* v___x_2090_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
v___x_2083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
v___x_2084_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_2085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
v___x_2086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1));
lean_inc(v_stx_2072_);
v___x_2087_ = l_Lean_Syntax_isOfKind(v_stx_2072_, v___x_2086_);
v___x_2088_ = lean_box(v___x_2087_);
v___y_2089_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed), 15, 6);
lean_closure_set(v___y_2089_, 0, v___x_2088_);
lean_closure_set(v___y_2089_, 1, v_stx_2072_);
lean_closure_set(v___y_2089_, 2, v___x_2082_);
lean_closure_set(v___y_2089_, 3, v___x_2083_);
lean_closure_set(v___y_2089_, 4, v___x_2084_);
lean_closure_set(v___y_2089_, 5, v___x_2085_);
v___x_2090_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_2089_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed(lean_object* v_stx_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(v_stx_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1(){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2107_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1));
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1));
v___x_2110_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed), 10, 0);
v___x_2111_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2107_, v___x_2108_, v___x_2109_, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___boxed(lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
return v_res_2113_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(lean_object* v_numDigits_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_bs_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2127_ == 0)
{
return v_bs_2126_;
}
else
{
lean_object* v_v_2128_; lean_object* v_e_2129_; uint64_t v_anchor_2130_; lean_object* v___x_2131_; lean_object* v_bs_x27_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; double v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v_v_2128_ = lean_array_uget_borrowed(v_bs_2126_, v_i_2125_);
v_e_2129_ = lean_ctor_get(v_v_2128_, 2);
lean_inc_ref(v_e_2129_);
v_anchor_2130_ = lean_ctor_get_uint64(v_v_2128_, sizeof(void*)*3);
v___x_2131_ = lean_unsigned_to_nat(0u);
v_bs_x27_2132_ = lean_array_uset(v_bs_2126_, v_i_2125_, v___x_2131_);
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1));
v___x_2134_ = lean_box(0);
v___x_2135_ = lean_float_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2);
v___x_2136_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2137_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2137_, 0, v___x_2133_);
lean_ctor_set(v___x_2137_, 1, v___x_2134_);
lean_ctor_set(v___x_2137_, 2, v___x_2136_);
lean_ctor_set_float(v___x_2137_, sizeof(void*)*3, v___x_2135_);
lean_ctor_set_float(v___x_2137_, sizeof(void*)*3 + 8, v___x_2135_);
lean_ctor_set_uint8(v___x_2137_, sizeof(void*)*3 + 16, v___x_2127_);
v___x_2138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3);
v___x_2139_ = l_Lean_Meta_Grind_anchorToString(v_numDigits_2123_, v_anchor_2130_);
v___x_2140_ = l_Lean_stringToMessageData(v___x_2139_);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2138_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_MessageData_ofExpr(v_e_2129_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0));
v___x_2147_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2137_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v___x_2146_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2125_, v___x_2148_);
v___x_2150_ = lean_array_uset(v_bs_x27_2132_, v_i_2125_, v___x_2147_);
v_i_2125_ = v___x_2149_;
v_bs_2126_ = v___x_2150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___boxed(lean_object* v_numDigits_2152_, lean_object* v_sz_2153_, lean_object* v_i_2154_, lean_object* v_bs_2155_){
_start:
{
size_t v_sz_boxed_2156_; size_t v_i_boxed_2157_; lean_object* v_res_2158_; 
v_sz_boxed_2156_ = lean_unbox_usize(v_sz_2153_);
lean_dec(v_sz_2153_);
v_i_boxed_2157_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(v_numDigits_2152_, v_sz_boxed_2156_, v_i_boxed_2157_, v_bs_2155_);
lean_dec(v_numDigits_2152_);
return v_res_2158_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2162_; uint8_t v___x_2163_; double v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2163_ = 0;
v___x_2164_ = lean_float_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2);
v___x_2165_ = lean_box(0);
v___x_2166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1));
v___x_2167_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2165_);
lean_ctor_set(v___x_2167_, 2, v___x_2162_);
lean_ctor_set_float(v___x_2167_, sizeof(void*)*3, v___x_2164_);
lean_ctor_set_float(v___x_2167_, sizeof(void*)*3 + 8, v___x_2164_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 16, v___x_2163_);
return v___x_2167_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4));
v___x_2172_ = l_Lean_MessageData_ofFormat(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(uint8_t v___x_2176_, lean_object* v_stx_2177_, lean_object* v___x_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
if (v___x_2176_ == 0)
{
lean_object* v___x_2191_; 
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2180_);
lean_dec_ref(v___x_2179_);
lean_dec_ref(v___x_2178_);
v___x_2191_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = l_Lean_Syntax_getArg(v_stx_2177_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2));
v___x_2195_ = l_Lean_Name_mkStr5(v___x_2178_, v___x_2179_, v___x_2180_, v___x_2181_, v___x_2194_);
lean_inc(v___x_2193_);
v___x_2196_ = l_Lean_Syntax_isOfKind(v___x_2193_, v___x_2195_);
lean_dec(v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
lean_dec(v___x_2193_);
v___x_2197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v_filter_x3f_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2256_ = l_Lean_Syntax_getArg(v___x_2193_, v___x_2198_);
lean_dec(v___x_2193_);
v___x_2257_ = l_Lean_Syntax_isNone(v___x_2256_);
if (v___x_2257_ == 0)
{
uint8_t v___x_2258_; 
lean_inc(v___x_2256_);
v___x_2258_ = l_Lean_Syntax_matchesNull(v___x_2256_, v___x_2192_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec(v___x_2256_);
v___x_2259_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_2259_;
}
else
{
lean_object* v_filter_x3f_2260_; lean_object* v___x_2261_; 
v_filter_x3f_2260_ = l_Lean_Syntax_getArg(v___x_2256_, v___x_2198_);
lean_dec(v___x_2256_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v_filter_x3f_2260_);
v_filter_x3f_2218_ = v___x_2261_;
v___y_2219_ = v___y_2182_;
v___y_2220_ = v___y_2183_;
v___y_2221_ = v___y_2184_;
v___y_2222_ = v___y_2185_;
v___y_2223_ = v___y_2186_;
v___y_2224_ = v___y_2187_;
v___y_2225_ = v___y_2188_;
v___y_2226_ = v___y_2189_;
goto v___jp_2217_;
}
}
else
{
lean_object* v___x_2262_; 
lean_dec(v___x_2256_);
v___x_2262_ = lean_box(0);
v_filter_x3f_2218_ = v___x_2262_;
v___y_2219_ = v___y_2182_;
v___y_2220_ = v___y_2183_;
v___y_2221_ = v___y_2184_;
v___y_2222_ = v___y_2185_;
v___y_2223_ = v___y_2186_;
v___y_2224_ = v___y_2187_;
v___y_2225_ = v___y_2188_;
v___y_2226_ = v___y_2189_;
goto v___jp_2217_;
}
v___jp_2199_:
{
size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_sz_2210_ = lean_array_size(v___y_2200_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(v___y_2201_, v_sz_2210_, v___x_2211_, v___y_2200_);
lean_dec(v___y_2201_);
v___x_2213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2);
v___x_2214_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5);
v___x_2215_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
lean_ctor_set(v___x_2215_, 2, v___x_2212_);
v___x_2216_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v___x_2215_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2216_;
}
v___jp_2217_:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Elab_Tactic_Grind_elabFilter(v_filter_x3f_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Filter_eval___boxed), 13, 1);
lean_closure_set(v___x_2229_, 0, v_a_2228_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed), 13, 2);
lean_closure_set(v___x_2231_, 0, v___x_2229_);
lean_closure_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_2231_, v___y_2219_, v___y_2220_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v_candidates_2234_; lean_object* v_numDigits_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_candidates_2234_ = lean_ctor_get(v_a_2233_, 0);
lean_inc_ref(v_candidates_2234_);
v_numDigits_2235_ = lean_ctor_get(v_a_2233_, 1);
lean_inc(v_numDigits_2235_);
lean_dec(v_a_2233_);
v___x_2236_ = lean_array_get_size(v_candidates_2234_);
v___x_2237_ = lean_nat_dec_eq(v___x_2236_, v___x_2198_);
if (v___x_2237_ == 0)
{
v___y_2200_ = v_candidates_2234_;
v___y_2201_ = v_numDigits_2235_;
v___y_2202_ = v___y_2219_;
v___y_2203_ = v___y_2220_;
v___y_2204_ = v___y_2221_;
v___y_2205_ = v___y_2222_;
v___y_2206_ = v___y_2223_;
v___y_2207_ = v___y_2224_;
v___y_2208_ = v___y_2225_;
v___y_2209_ = v___y_2226_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v_numDigits_2235_);
lean_dec_ref(v_candidates_2234_);
v___x_2238_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7);
v___x_2239_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_2238_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2239_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_a_2240_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2232_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2232_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2227_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2227_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed(lean_object* v___x_2263_, lean_object* v_stx_2264_, lean_object* v___x_2265_, lean_object* v___x_2266_, lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v___x_1375__boxed_2278_; lean_object* v_res_2279_; 
v___x_1375__boxed_2278_ = lean_unbox(v___x_2263_);
v_res_2279_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(v___x_1375__boxed_2278_, v_stx_2264_, v___x_2265_, v___x_2266_, v___x_2267_, v___x_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v_stx_2264_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(lean_object* v_stx_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___y_2304_; lean_object* v___x_2305_; 
v___x_2297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0));
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1));
v___x_2299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_2300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2));
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1));
lean_inc(v_stx_2287_);
v___x_2302_ = l_Lean_Syntax_isOfKind(v_stx_2287_, v___x_2301_);
v___x_2303_ = lean_box(v___x_2302_);
v___y_2304_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed), 15, 6);
lean_closure_set(v___y_2304_, 0, v___x_2303_);
lean_closure_set(v___y_2304_, 1, v_stx_2287_);
lean_closure_set(v___y_2304_, 2, v___x_2297_);
lean_closure_set(v___y_2304_, 3, v___x_2298_);
lean_closure_set(v___y_2304_, 4, v___x_2299_);
lean_closure_set(v___y_2304_, 5, v___x_2300_);
v___x_2305_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_2304_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed(lean_object* v_stx_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(v_stx_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1(){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2322_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1));
v___x_2324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1));
v___x_2325_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed), 10, 0);
v___x_2326_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2322_, v___x_2323_, v___x_2324_, v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___boxed(lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg(uint64_t v_a_2329_, lean_object* v_b_2330_, lean_object* v_x_2331_){
_start:
{
if (lean_obj_tag(v_x_2331_) == 0)
{
lean_dec(v_b_2330_);
return v_x_2331_;
}
else
{
lean_object* v_key_2332_; lean_object* v_value_2333_; lean_object* v_tail_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2348_; 
v_key_2332_ = lean_ctor_get(v_x_2331_, 0);
v_value_2333_ = lean_ctor_get(v_x_2331_, 1);
v_tail_2334_ = lean_ctor_get(v_x_2331_, 2);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2331_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2336_ = v_x_2331_;
v_isShared_2337_ = v_isSharedCheck_2348_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_tail_2334_);
lean_inc(v_value_2333_);
lean_inc(v_key_2332_);
lean_dec(v_x_2331_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2348_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint64_t v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = lean_unbox_uint64(v_key_2332_);
v___x_2339_ = lean_uint64_dec_eq(v___x_2338_, v_a_2329_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg(v_a_2329_, v_b_2330_, v_tail_2334_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 2, v___x_2340_);
v___x_2342_ = v___x_2336_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_key_2332_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_value_2333_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
lean_dec(v_value_2333_);
lean_dec(v_key_2332_);
v___x_2344_ = lean_box_uint64(v_a_2329_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v_b_2330_);
lean_ctor_set(v___x_2336_, 0, v___x_2344_);
v___x_2346_ = v___x_2336_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_b_2330_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_tail_2334_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_a_2349_, lean_object* v_b_2350_, lean_object* v_x_2351_){
_start:
{
uint64_t v_a_boxed_2352_; lean_object* v_res_2353_; 
v_a_boxed_2352_ = lean_unbox_uint64(v_a_2349_);
lean_dec_ref(v_a_2349_);
v_res_2353_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg(v_a_boxed_2352_, v_b_2350_, v_x_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
if (lean_obj_tag(v_x_2355_) == 0)
{
return v_x_2354_;
}
else
{
lean_object* v_key_2356_; lean_object* v_value_2357_; lean_object* v_tail_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2382_; 
v_key_2356_ = lean_ctor_get(v_x_2355_, 0);
v_value_2357_ = lean_ctor_get(v_x_2355_, 1);
v_tail_2358_ = lean_ctor_get(v_x_2355_, 2);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2360_ = v_x_2355_;
v_isShared_2361_ = v_isSharedCheck_2382_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_tail_2358_);
lean_inc(v_value_2357_);
lean_inc(v_key_2356_);
lean_dec(v_x_2355_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2382_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; uint64_t v___x_2363_; uint64_t v___x_2364_; uint64_t v___x_2365_; uint64_t v___x_2366_; uint64_t v_fold_2367_; uint64_t v___x_2368_; uint64_t v___x_2369_; uint64_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2362_ = lean_array_get_size(v_x_2354_);
v___x_2363_ = 32ULL;
v___x_2364_ = lean_unbox_uint64(v_key_2356_);
v___x_2365_ = lean_uint64_shift_right(v___x_2364_, v___x_2363_);
v___x_2366_ = lean_unbox_uint64(v_key_2356_);
v_fold_2367_ = lean_uint64_xor(v___x_2366_, v___x_2365_);
v___x_2368_ = 16ULL;
v___x_2369_ = lean_uint64_shift_right(v_fold_2367_, v___x_2368_);
v___x_2370_ = lean_uint64_xor(v_fold_2367_, v___x_2369_);
v___x_2371_ = lean_uint64_to_usize(v___x_2370_);
v___x_2372_ = lean_usize_of_nat(v___x_2362_);
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_sub(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_usize_land(v___x_2371_, v___x_2374_);
v___x_2376_ = lean_array_uget_borrowed(v_x_2354_, v___x_2375_);
lean_inc(v___x_2376_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 2, v___x_2376_);
v___x_2378_ = v___x_2360_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_key_2356_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_value_2357_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_array_uset(v_x_2354_, v___x_2375_, v___x_2378_);
v_x_2354_ = v___x_2379_;
v_x_2355_ = v_tail_2358_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(lean_object* v_i_2383_, lean_object* v_source_2384_, lean_object* v_target_2385_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_array_get_size(v_source_2384_);
v___x_2387_ = lean_nat_dec_lt(v_i_2383_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_dec_ref(v_source_2384_);
lean_dec(v_i_2383_);
return v_target_2385_;
}
else
{
lean_object* v_es_2388_; lean_object* v___x_2389_; lean_object* v_source_2390_; lean_object* v_target_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_es_2388_ = lean_array_fget(v_source_2384_, v_i_2383_);
v___x_2389_ = lean_box(0);
v_source_2390_ = lean_array_fset(v_source_2384_, v_i_2383_, v___x_2389_);
v_target_2391_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_target_2385_, v_es_2388_);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_nat_add(v_i_2383_, v___x_2392_);
lean_dec(v_i_2383_);
v_i_2383_ = v___x_2393_;
v_source_2384_ = v_source_2390_;
v_target_2385_ = v_target_2391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_data_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v_nbuckets_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2396_ = lean_array_get_size(v_data_2395_);
v___x_2397_ = lean_unsigned_to_nat(2u);
v_nbuckets_2398_ = lean_nat_mul(v___x_2396_, v___x_2397_);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_box(0);
v___x_2401_ = lean_mk_array(v_nbuckets_2398_, v___x_2400_);
v___x_2402_ = lean_array_propagate_mark(v_data_2395_, v___x_2401_);
v___x_2403_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v___x_2399_, v_data_2395_, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(uint64_t v_a_2404_, lean_object* v_x_2405_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 0)
{
uint8_t v___x_2406_; 
v___x_2406_ = 0;
return v___x_2406_;
}
else
{
lean_object* v_key_2407_; lean_object* v_tail_2408_; uint64_t v___x_2409_; uint8_t v___x_2410_; 
v_key_2407_ = lean_ctor_get(v_x_2405_, 0);
v_tail_2408_ = lean_ctor_get(v_x_2405_, 2);
v___x_2409_ = lean_unbox_uint64(v_key_2407_);
v___x_2410_ = lean_uint64_dec_eq(v___x_2409_, v_a_2404_);
if (v___x_2410_ == 0)
{
v_x_2405_ = v_tail_2408_;
goto _start;
}
else
{
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2412_, lean_object* v_x_2413_){
_start:
{
uint64_t v_a_boxed_2414_; uint8_t v_res_2415_; lean_object* v_r_2416_; 
v_a_boxed_2414_ = lean_unbox_uint64(v_a_2412_);
lean_dec_ref(v_a_2412_);
v_res_2415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(v_a_boxed_2414_, v_x_2413_);
lean_dec(v_x_2413_);
v_r_2416_ = lean_box(v_res_2415_);
return v_r_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(lean_object* v_m_2417_, uint64_t v_a_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v_size_2420_; lean_object* v_buckets_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2464_; 
v_size_2420_ = lean_ctor_get(v_m_2417_, 0);
v_buckets_2421_ = lean_ctor_get(v_m_2417_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_m_2417_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2423_ = v_m_2417_;
v_isShared_2424_ = v_isSharedCheck_2464_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_buckets_2421_);
lean_inc(v_size_2420_);
lean_dec(v_m_2417_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2464_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; uint64_t v___x_2426_; uint64_t v___x_2427_; uint64_t v_fold_2428_; uint64_t v___x_2429_; uint64_t v___x_2430_; uint64_t v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; lean_object* v_bkt_2437_; uint8_t v___x_2438_; 
v___x_2425_ = lean_array_get_size(v_buckets_2421_);
v___x_2426_ = 32ULL;
v___x_2427_ = lean_uint64_shift_right(v_a_2418_, v___x_2426_);
v_fold_2428_ = lean_uint64_xor(v_a_2418_, v___x_2427_);
v___x_2429_ = 16ULL;
v___x_2430_ = lean_uint64_shift_right(v_fold_2428_, v___x_2429_);
v___x_2431_ = lean_uint64_xor(v_fold_2428_, v___x_2430_);
v___x_2432_ = lean_uint64_to_usize(v___x_2431_);
v___x_2433_ = lean_usize_of_nat(v___x_2425_);
v___x_2434_ = ((size_t)1ULL);
v___x_2435_ = lean_usize_sub(v___x_2433_, v___x_2434_);
v___x_2436_ = lean_usize_land(v___x_2432_, v___x_2435_);
v_bkt_2437_ = lean_array_uget_borrowed(v_buckets_2421_, v___x_2436_);
v___x_2438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2418_, v_bkt_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v_size_x27_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_buckets_x27_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2439_ = lean_unsigned_to_nat(1u);
v_size_x27_2440_ = lean_nat_add(v_size_2420_, v___x_2439_);
lean_dec(v_size_2420_);
v___x_2441_ = lean_box_uint64(v_a_2418_);
lean_inc(v_bkt_2437_);
v___x_2442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v_b_2419_);
lean_ctor_set(v___x_2442_, 2, v_bkt_2437_);
v_buckets_x27_2443_ = lean_array_uset(v_buckets_2421_, v___x_2436_, v___x_2442_);
v___x_2444_ = lean_unsigned_to_nat(4u);
v___x_2445_ = lean_nat_mul(v_size_x27_2440_, v___x_2444_);
v___x_2446_ = lean_unsigned_to_nat(3u);
v___x_2447_ = lean_nat_div(v___x_2445_, v___x_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_array_get_size(v_buckets_x27_2443_);
v___x_2449_ = lean_nat_dec_le(v___x_2447_, v___x_2448_);
lean_dec(v___x_2447_);
if (v___x_2449_ == 0)
{
lean_object* v_val_2450_; lean_object* v___x_2452_; 
v_val_2450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6___redArg(v_buckets_x27_2443_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v_val_2450_);
lean_ctor_set(v___x_2423_, 0, v_size_x27_2440_);
v___x_2452_ = v___x_2423_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_size_x27_2440_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_val_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
lean_object* v___x_2455_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v_buckets_x27_2443_);
lean_ctor_set(v___x_2423_, 0, v_size_x27_2440_);
v___x_2455_ = v___x_2423_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_size_x27_2440_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_buckets_x27_2443_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v___x_2457_; lean_object* v_buckets_x27_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_inc(v_bkt_2437_);
v___x_2457_ = lean_box(0);
v_buckets_x27_2458_ = lean_array_uset(v_buckets_2421_, v___x_2436_, v___x_2457_);
v___x_2459_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg(v_a_2418_, v_b_2419_, v_bkt_2437_);
v___x_2460_ = lean_array_uset(v_buckets_x27_2458_, v___x_2436_, v___x_2459_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v___x_2460_);
v___x_2462_ = v___x_2423_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_size_2420_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_2465_, lean_object* v_a_2466_, lean_object* v_b_2467_){
_start:
{
uint64_t v_a_boxed_2468_; lean_object* v_res_2469_; 
v_a_boxed_2468_ = lean_unbox_uint64(v_a_2466_);
lean_dec_ref(v_a_2466_);
v_res_2469_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(v_m_2465_, v_a_boxed_2468_, v_b_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(uint64_t v_a_2470_, lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_box(0);
return v___x_2472_;
}
else
{
lean_object* v_key_2473_; lean_object* v_value_2474_; lean_object* v_tail_2475_; uint64_t v___x_2476_; uint8_t v___x_2477_; 
v_key_2473_ = lean_ctor_get(v_x_2471_, 0);
v_value_2474_ = lean_ctor_get(v_x_2471_, 1);
v_tail_2475_ = lean_ctor_get(v_x_2471_, 2);
v___x_2476_ = lean_unbox_uint64(v_key_2473_);
v___x_2477_ = lean_uint64_dec_eq(v___x_2476_, v_a_2470_);
if (v___x_2477_ == 0)
{
v_x_2471_ = v_tail_2475_;
goto _start;
}
else
{
lean_object* v___x_2479_; 
lean_inc(v_value_2474_);
v___x_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_value_2474_);
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_2480_, lean_object* v_x_2481_){
_start:
{
uint64_t v_a_boxed_2482_; lean_object* v_res_2483_; 
v_a_boxed_2482_ = lean_unbox_uint64(v_a_2480_);
lean_dec_ref(v_a_2480_);
v_res_2483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_boxed_2482_, v_x_2481_);
lean_dec(v_x_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(lean_object* v_m_2484_, uint64_t v_a_2485_){
_start:
{
lean_object* v_buckets_2486_; lean_object* v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v_fold_2490_; uint64_t v___x_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_buckets_2486_ = lean_ctor_get(v_m_2484_, 1);
v___x_2487_ = lean_array_get_size(v_buckets_2486_);
v___x_2488_ = 32ULL;
v___x_2489_ = lean_uint64_shift_right(v_a_2485_, v___x_2488_);
v_fold_2490_ = lean_uint64_xor(v_a_2485_, v___x_2489_);
v___x_2491_ = 16ULL;
v___x_2492_ = lean_uint64_shift_right(v_fold_2490_, v___x_2491_);
v___x_2493_ = lean_uint64_xor(v_fold_2490_, v___x_2492_);
v___x_2494_ = lean_uint64_to_usize(v___x_2493_);
v___x_2495_ = lean_usize_of_nat(v___x_2487_);
v___x_2496_ = ((size_t)1ULL);
v___x_2497_ = lean_usize_sub(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_usize_land(v___x_2494_, v___x_2497_);
v___x_2499_ = lean_array_uget_borrowed(v_buckets_2486_, v___x_2498_);
v___x_2500_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_2485_, v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_2501_, lean_object* v_a_2502_){
_start:
{
uint64_t v_a_boxed_2503_; lean_object* v_res_2504_; 
v_a_boxed_2503_ = lean_unbox_uint64(v_a_2502_);
lean_dec_ref(v_a_2502_);
v_res_2504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(v_m_2501_, v_a_boxed_2503_);
lean_dec_ref(v_m_2501_);
return v_res_2504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_unsigned_to_nat(16u);
v___x_2507_ = lean_mk_array(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v_found_2510_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0);
v___x_2509_ = lean_unsigned_to_nat(0u);
v_found_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_2510_, 0, v___x_2509_);
lean_ctor_set(v_found_2510_, 1, v___x_2508_);
return v_found_2510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v_found_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_found_2511_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1);
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v_found_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(lean_object* v_shift_2514_, lean_object* v_numDigits_2515_, lean_object* v_es_2516_, lean_object* v_as_2517_, size_t v_sz_2518_, size_t v_i_2519_, lean_object* v_b_2520_){
_start:
{
lean_object* v_a_2522_; uint8_t v___x_2526_; 
v___x_2526_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
if (v___x_2526_ == 0)
{
return v_b_2520_;
}
else
{
lean_object* v_snd_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2561_; 
v_snd_2527_ = lean_ctor_get(v_b_2520_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_b_2520_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v_b_2520_, 0);
lean_dec(v_unused_2562_);
v___x_2529_ = v_b_2520_;
v_isShared_2530_ = v_isSharedCheck_2561_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_snd_2527_);
lean_dec(v_b_2520_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2561_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v_a_2531_; uint64_t v_anchor_2532_; lean_object* v___x_2533_; uint64_t v___x_2534_; uint64_t v___x_2535_; lean_object* v___x_2536_; 
v_a_2531_ = lean_array_uget_borrowed(v_as_2517_, v_i_2519_);
v_anchor_2532_ = lean_ctor_get_uint64(v_a_2531_, sizeof(void*)*1);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_uint64_of_nat(v_shift_2514_);
v___x_2535_ = lean_uint64_shift_right(v_anchor_2532_, v___x_2534_);
v___x_2536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(v_snd_2527_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 1)
{
lean_object* v_val_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2555_; 
v_val_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2555_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_val_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2555_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
uint64_t v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = lean_unbox_uint64(v_val_2537_);
lean_dec(v_val_2537_);
v___x_2542_ = lean_uint64_dec_eq(v___x_2541_, v_anchor_2532_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = lean_nat_add(v_numDigits_2515_, v___x_2543_);
v___x_2545_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(v_es_2516_, v___x_2544_);
lean_dec(v___x_2544_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2545_);
v___x_2547_ = v___x_2539_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2547_);
v___x_2549_ = v___x_2529_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_snd_2527_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v___x_2553_; 
lean_del_object(v___x_2539_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2533_);
v___x_2553_ = v___x_2529_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_snd_2527_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
v_a_2522_ = v___x_2553_;
goto v___jp_2521_;
}
}
}
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_dec(v___x_2536_);
v___x_2556_ = lean_box_uint64(v_anchor_2532_);
v___x_2557_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(v_snd_2527_, v___x_2535_, v___x_2556_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2557_);
lean_ctor_set(v___x_2529_, 0, v___x_2533_);
v___x_2559_ = v___x_2529_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
v_a_2522_ = v___x_2559_;
goto v___jp_2521_;
}
}
}
}
v___jp_2521_:
{
size_t v___x_2523_; size_t v___x_2524_; 
v___x_2523_ = ((size_t)1ULL);
v___x_2524_ = lean_usize_add(v_i_2519_, v___x_2523_);
v_i_2519_ = v___x_2524_;
v_b_2520_ = v_a_2522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(lean_object* v_es_2563_, lean_object* v_numDigits_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2565_ = lean_unsigned_to_nat(4u);
v___x_2566_ = lean_nat_mul(v___x_2565_, v_numDigits_2564_);
v___x_2567_ = lean_unsigned_to_nat(64u);
v___x_2568_ = lean_nat_dec_lt(v___x_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_dec(v___x_2566_);
lean_inc(v_numDigits_2564_);
return v_numDigits_2564_;
}
else
{
lean_object* v_shift_2569_; lean_object* v___x_2570_; size_t v_sz_2571_; size_t v___x_2572_; lean_object* v___x_2573_; lean_object* v_fst_2574_; 
v_shift_2569_ = lean_nat_sub(v___x_2567_, v___x_2566_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2);
v_sz_2571_ = lean_array_size(v_es_2563_);
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(v_shift_2569_, v_numDigits_2564_, v_es_2563_, v_es_2563_, v_sz_2571_, v___x_2572_, v___x_2570_);
lean_dec(v_shift_2569_);
v_fst_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_fst_2574_);
lean_dec_ref(v___x_2573_);
if (lean_obj_tag(v_fst_2574_) == 0)
{
lean_inc(v_numDigits_2564_);
return v_numDigits_2564_;
}
else
{
lean_object* v_val_2575_; 
v_val_2575_ = lean_ctor_get(v_fst_2574_, 0);
lean_inc(v_val_2575_);
lean_dec_ref_known(v_fst_2574_, 1);
return v_val_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___boxed(lean_object* v_es_2576_, lean_object* v_numDigits_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(v_es_2576_, v_numDigits_2577_);
lean_dec(v_numDigits_2577_);
lean_dec_ref(v_es_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3___boxed(lean_object* v_shift_2579_, lean_object* v_numDigits_2580_, lean_object* v_es_2581_, lean_object* v_as_2582_, lean_object* v_sz_2583_, lean_object* v_i_2584_, lean_object* v_b_2585_){
_start:
{
size_t v_sz_boxed_2586_; size_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_sz_boxed_2586_ = lean_unbox_usize(v_sz_2583_);
lean_dec(v_sz_2583_);
v_i_boxed_2587_ = lean_unbox_usize(v_i_2584_);
lean_dec(v_i_2584_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(v_shift_2579_, v_numDigits_2580_, v_es_2581_, v_as_2582_, v_sz_boxed_2586_, v_i_boxed_2587_, v_b_2585_);
lean_dec_ref(v_as_2582_);
lean_dec_ref(v_es_2581_);
lean_dec(v_numDigits_2580_);
lean_dec(v_shift_2579_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(lean_object* v_es_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_unsigned_to_nat(4u);
v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(v_es_2589_, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0___boxed(lean_object* v_es_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(v_es_2592_);
lean_dec_ref(v_es_2592_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(lean_object* v___x_2597_, size_t v_sz_2598_, size_t v_i_2599_, lean_object* v_bs_2600_){
_start:
{
uint8_t v___x_2601_; 
v___x_2601_ = lean_usize_dec_lt(v_i_2599_, v_sz_2598_);
if (v___x_2601_ == 0)
{
return v_bs_2600_;
}
else
{
lean_object* v_v_2602_; lean_object* v_e_2603_; uint64_t v_anchor_2604_; lean_object* v___x_2605_; lean_object* v_bs_x27_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; double v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; size_t v___x_2622_; size_t v___x_2623_; lean_object* v___x_2624_; 
v_v_2602_ = lean_array_uget_borrowed(v_bs_2600_, v_i_2599_);
v_e_2603_ = lean_ctor_get(v_v_2602_, 0);
lean_inc_ref(v_e_2603_);
v_anchor_2604_ = lean_ctor_get_uint64(v_v_2602_, sizeof(void*)*1);
v___x_2605_ = lean_unsigned_to_nat(0u);
v_bs_x27_2606_ = lean_array_uset(v_bs_2600_, v_i_2599_, v___x_2605_);
v___x_2607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1));
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_float_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2);
v___x_2610_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2611_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2611_, 0, v___x_2607_);
lean_ctor_set(v___x_2611_, 1, v___x_2608_);
lean_ctor_set(v___x_2611_, 2, v___x_2610_);
lean_ctor_set_float(v___x_2611_, sizeof(void*)*3, v___x_2609_);
lean_ctor_set_float(v___x_2611_, sizeof(void*)*3 + 8, v___x_2609_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*3 + 16, v___x_2601_);
v___x_2612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3);
v___x_2613_ = l_Lean_Meta_Grind_anchorToString(v___x_2597_, v_anchor_2604_);
v___x_2614_ = l_Lean_stringToMessageData(v___x_2613_);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2612_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Lean_MessageData_ofExpr(v_e_2603_);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0));
v___x_2621_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2611_);
lean_ctor_set(v___x_2621_, 1, v___x_2619_);
lean_ctor_set(v___x_2621_, 2, v___x_2620_);
v___x_2622_ = ((size_t)1ULL);
v___x_2623_ = lean_usize_add(v_i_2599_, v___x_2622_);
v___x_2624_ = lean_array_uset(v_bs_x27_2606_, v_i_2599_, v___x_2621_);
v_i_2599_ = v___x_2623_;
v_bs_2600_ = v___x_2624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___boxed(lean_object* v___x_2626_, lean_object* v_sz_2627_, lean_object* v_i_2628_, lean_object* v_bs_2629_){
_start:
{
size_t v_sz_boxed_2630_; size_t v_i_boxed_2631_; lean_object* v_res_2632_; 
v_sz_boxed_2630_ = lean_unbox_usize(v_sz_2627_);
lean_dec(v_sz_2627_);
v_i_boxed_2631_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(v___x_2626_, v_sz_boxed_2630_, v_i_boxed_2631_, v_bs_2629_);
lean_dec(v___x_2626_);
return v_res_2632_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; double v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2636_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2637_ = 0;
v___x_2638_ = lean_float_once(&l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2, &l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2);
v___x_2639_ = lean_box(0);
v___x_2640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1));
v___x_2641_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
lean_ctor_set(v___x_2641_, 1, v___x_2639_);
lean_ctor_set(v___x_2641_, 2, v___x_2636_);
lean_ctor_set_float(v___x_2641_, sizeof(void*)*3, v___x_2638_);
lean_ctor_set_float(v___x_2641_, sizeof(void*)*3 + 8, v___x_2638_);
lean_ctor_set_uint8(v___x_2641_, sizeof(void*)*3 + 16, v___x_2637_);
return v___x_2641_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4));
v___x_2646_ = l_Lean_MessageData_ofFormat(v___x_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_2648_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getLocalTheoremAnchors___boxed), 11, 1);
lean_closure_set(v___x_2658_, 0, v_a_2657_);
v___x_2659_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_2658_, v___y_2647_, v___y_2648_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; size_t v_sz_2662_; size_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(v_a_2660_);
v_sz_2662_ = lean_array_size(v_a_2660_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(v___x_2661_, v_sz_2662_, v___x_2663_, v_a_2660_);
lean_dec(v___x_2661_);
v___x_2665_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2);
v___x_2666_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5);
v___x_2667_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
lean_ctor_set(v___x_2667_, 2, v___x_2664_);
v___x_2668_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v___x_2667_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
return v___x_2668_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
v_a_2669_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2659_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2659_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2656_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2656_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed(lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___f_2705_; lean_object* v___x_2706_; 
v___f_2705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0));
v___x_2706_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_2705_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___boxed(lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(lean_object* v_x_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed(lean_object* v_x_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(v_x_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_x_2728_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2739_, lean_object* v_m_2740_, uint64_t v_a_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(v_m_2740_, v_a_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2743_, lean_object* v_m_2744_, lean_object* v_a_2745_){
_start:
{
uint64_t v_a_boxed_2746_; lean_object* v_res_2747_; 
v_a_boxed_2746_ = lean_unbox_uint64(v_a_2745_);
lean_dec_ref(v_a_2745_);
v_res_2747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(v_00_u03b2_2743_, v_m_2744_, v_a_boxed_2746_);
lean_dec_ref(v_m_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2748_, lean_object* v_m_2749_, uint64_t v_a_2750_, lean_object* v_b_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(v_m_2749_, v_a_2750_, v_b_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2753_, lean_object* v_m_2754_, lean_object* v_a_2755_, lean_object* v_b_2756_){
_start:
{
uint64_t v_a_boxed_2757_; lean_object* v_res_2758_; 
v_a_boxed_2757_ = lean_unbox_uint64(v_a_2755_);
lean_dec_ref(v_a_2755_);
v_res_2758_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(v_00_u03b2_2753_, v_m_2754_, v_a_boxed_2757_, v_b_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2759_, uint64_t v_a_2760_, lean_object* v_x_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_2760_, v_x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2763_, lean_object* v_a_2764_, lean_object* v_x_2765_){
_start:
{
uint64_t v_a_boxed_2766_; lean_object* v_res_2767_; 
v_a_boxed_2766_ = lean_unbox_uint64(v_a_2764_);
lean_dec_ref(v_a_2764_);
v_res_2767_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2763_, v_a_boxed_2766_, v_x_2765_);
lean_dec(v_x_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2768_, uint64_t v_a_2769_, lean_object* v_x_2770_){
_start:
{
uint8_t v___x_2771_; 
v___x_2771_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2769_, v_x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2772_, lean_object* v_a_2773_, lean_object* v_x_2774_){
_start:
{
uint64_t v_a_boxed_2775_; uint8_t v_res_2776_; lean_object* v_r_2777_; 
v_a_boxed_2775_ = lean_unbox_uint64(v_a_2773_);
lean_dec_ref(v_a_2773_);
v_res_2776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_2772_, v_a_boxed_2775_, v_x_2774_);
lean_dec(v_x_2774_);
v_r_2777_ = lean_box(v_res_2776_);
return v_r_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2778_, lean_object* v_data_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6___redArg(v_data_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b2_2781_, uint64_t v_a_2782_, lean_object* v_b_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___redArg(v_a_2782_, v_b_2783_, v_x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2786_, lean_object* v_a_2787_, lean_object* v_b_2788_, lean_object* v_x_2789_){
_start:
{
uint64_t v_a_boxed_2790_; lean_object* v_res_2791_; 
v_a_boxed_2790_ = lean_unbox_uint64(v_a_2787_);
lean_dec_ref(v_a_2787_);
v_res_2791_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__7(v_00_u03b2_2786_, v_a_boxed_2790_, v_b_2788_, v_x_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7(lean_object* v_00_u03b2_2792_, lean_object* v_i_2793_, lean_object* v_source_2794_, lean_object* v_target_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_i_2793_, v_source_2794_, v_target_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_x_2798_, v_x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1(){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2813_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1));
v___x_2815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3));
v___x_2816_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed), 10, 0);
v___x_2817_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2813_, v___x_2814_, v___x_2815_, v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___boxed(lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(lean_object* v_e_2820_, lean_object* v___y_2821_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Lean_Expr_hasMVar(v_e_2820_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_e_2820_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; lean_object* v_mctx_2826_; lean_object* v___x_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___x_2830_; lean_object* v_cache_2831_; lean_object* v_zetaDeltaFVarIds_2832_; lean_object* v_postponed_2833_; lean_object* v_diag_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2843_; 
v___x_2825_ = lean_st_ref_get(v___y_2821_);
v_mctx_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_ref(v_mctx_2826_);
lean_dec(v___x_2825_);
v___x_2827_ = l_Lean_instantiateMVarsCore(v_mctx_2826_, v_e_2820_);
v_fst_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_fst_2828_);
v_snd_2829_ = lean_ctor_get(v___x_2827_, 1);
lean_inc(v_snd_2829_);
lean_dec_ref(v___x_2827_);
v___x_2830_ = lean_st_ref_take(v___y_2821_);
v_cache_2831_ = lean_ctor_get(v___x_2830_, 1);
v_zetaDeltaFVarIds_2832_ = lean_ctor_get(v___x_2830_, 2);
v_postponed_2833_ = lean_ctor_get(v___x_2830_, 3);
v_diag_2834_ = lean_ctor_get(v___x_2830_, 4);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2830_, 0);
lean_dec(v_unused_2844_);
v___x_2836_ = v___x_2830_;
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_diag_2834_);
lean_inc(v_postponed_2833_);
lean_inc(v_zetaDeltaFVarIds_2832_);
lean_inc(v_cache_2831_);
lean_dec(v___x_2830_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_snd_2829_);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_snd_2829_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_cache_2831_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_zetaDeltaFVarIds_2832_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_postponed_2833_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_diag_2834_);
v___x_2839_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_st_ref_put(v___y_2821_, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_fst_2828_);
return v___x_2841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg___boxed(lean_object* v_e_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(v_e_2845_, v___y_2846_);
lean_dec(v___y_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(lean_object* v_e_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(v_e_2849_, v___y_2855_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___boxed(lean_object* v_e_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(v_e_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; 
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
v___x_2881_ = lean_apply_9(v_x_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, lean_box(0));
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed(lean_object* v_x_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(v_x_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(lean_object* v_mvarId_2893_, lean_object* v_x_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___f_2904_; lean_object* v___x_2905_; 
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
lean_inc(v___y_2896_);
lean_inc_ref(v___y_2895_);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2904_, 0, v_x_2894_);
lean_closure_set(v___f_2904_, 1, v___y_2895_);
lean_closure_set(v___f_2904_, 2, v___y_2896_);
lean_closure_set(v___f_2904_, 3, v___y_2897_);
lean_closure_set(v___f_2904_, 4, v___y_2898_);
v___x_2905_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2893_, v___f_2904_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2905_) == 0)
{
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___boxed(lean_object* v_mvarId_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(v_mvarId_2914_, v_x_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(lean_object* v_00_u03b1_2926_, lean_object* v_mvarId_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(v_mvarId_2927_, v_x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___boxed(lean_object* v_00_u03b1_2939_, lean_object* v_mvarId_2940_, lean_object* v_x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(v_00_u03b1_2939_, v_mvarId_2940_, v_x_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(lean_object* v___x_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2962_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(v___x_2952_, v___y_2958_);
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref(v___x_2962_);
v___x_2964_ = l_Lean_MessageData_ofExpr(v_a_2963_);
v___x_2965_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v___x_2964_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed(lean_object* v___x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(v___x_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(lean_object* v_stx_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1));
lean_inc(v_stx_2991_);
v___x_3002_ = l_Lean_Syntax_isOfKind(v_stx_2991_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
lean_dec(v_stx_2991_);
v___x_3003_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = l_Lean_Syntax_getArg(v_stx_2991_, v___x_3004_);
lean_dec(v_stx_2991_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3));
lean_inc(v___x_3005_);
v___x_3007_ = l_Lean_Syntax_isOfKind(v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec(v___x_3005_);
v___x_3008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_2993_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v_mvarId_3011_; lean_object* v___x_3012_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v_mvarId_3011_ = lean_ctor_get(v_a_3010_, 1);
lean_inc(v_mvarId_3011_);
lean_dec(v_a_3010_);
v___x_3012_ = l_Lean_Elab_Tactic_Grind_evalGrindTactic(v___x_3005_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; 
lean_dec_ref_known(v___x_3012_, 1);
lean_inc(v_mvarId_3011_);
v___x_3013_ = l_Lean_mkMVar(v_mvarId_3011_);
v___f_3014_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3014_, 0, v___x_3013_);
v___x_3015_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(v_mvarId_3011_, v___f_3014_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
return v___x_3015_;
}
else
{
lean_dec(v_mvarId_3011_);
return v___x_3012_;
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v___x_3005_);
v_a_3016_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3009_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3009_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed(lean_object* v_stx_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(v_stx_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1(){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3040_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1));
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1));
v___x_3043_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed), 10, 0);
v___x_3044_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3040_, v___x_3041_, v___x_3042_, v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___boxed(lean_object* v_a_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
return v_res_3046_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_ShowState(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_ShowState(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Filter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_ShowState(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
}
#ifdef __cplusplus
}
#endif
