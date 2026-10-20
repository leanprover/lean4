// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.MatchUtil public import Lean.Meta.KAbstract public import Lean.Meta.Tactic.Apply public import Lean.Meta.BinderNameHint
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "Invalid rewrite argument: Expected an equality or iff proof or definition name, but"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__0 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__1;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "is "};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__2 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__3;
static const lean_array_object l_Lean_MVarId_rewrite___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__4 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__4_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__5 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__6 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__6_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Motive is dependent:"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__7 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__8;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "The rewrite tactic cannot substitute terms on which the type of the target expression depends. The type of the expression"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__9 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__10;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\ndepends on the value"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__11 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__11_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__12;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_a"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__13 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(228, 106, 112, 29, 6, 211, 214, 169)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__14 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__14_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "motive is not type correct:"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__15 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__16;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nError: "};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__17 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__17_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__18;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 353, .m_capacity = 353, .m_length = 352, .m_data = "\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__19 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__20;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "' implies that 'm a = m b', which can be used with lemmas such as '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__21 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__22;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__23 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__23_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__24_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__25_value_aux_0),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__25_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 348, .m_capacity = 348, .m_length = 347, .m_data = "' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__26 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__26_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__27;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__28 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__28_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__29 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__29_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well)."};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__30 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__30_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__31;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Did not find an occurrence of the pattern"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__32 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__32_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__33;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "\nin the target expression"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__34 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__34_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__35;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "Invalid rewrite argument: The pattern to be substituted is a metavariable (`"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__36 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__36_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__37;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "`) in this equality"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__38 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__38_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__39;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "a value of type"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__40 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__40_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "a proof of"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__41 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__41_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__42 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__42_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__43 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__43_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__44 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__44_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__45 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__45_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__46;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_rewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_MVarId_rewrite___closed__0 = (const lean_object*)&l_Lean_MVarId_rewrite___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 67, 55, 19, 78, 216, 184, 166)}};
static const lean_object* l_Lean_MVarId_rewrite___closed__1 = (const lean_object*)&l_Lean_MVarId_rewrite___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(lean_object* v_opts_44_, lean_object* v_opt_45_){
_start:
{
lean_object* v_name_46_; lean_object* v_defValue_47_; lean_object* v_map_48_; lean_object* v___x_49_; 
v_name_46_ = lean_ctor_get(v_opt_45_, 0);
v_defValue_47_ = lean_ctor_get(v_opt_45_, 1);
v_map_48_ = lean_ctor_get(v_opts_44_, 0);
v___x_49_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_48_, v_name_46_);
if (lean_obj_tag(v___x_49_) == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_unbox(v_defValue_47_);
return v___x_50_;
}
else
{
lean_object* v_val_51_; 
v_val_51_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_val_51_);
lean_dec_ref_known(v___x_49_, 1);
if (lean_obj_tag(v_val_51_) == 1)
{
uint8_t v_v_52_; 
v_v_52_ = lean_ctor_get_uint8(v_val_51_, 0);
lean_dec_ref_known(v_val_51_, 0);
return v_v_52_;
}
else
{
uint8_t v___x_53_; 
lean_dec(v_val_51_);
v___x_53_ = lean_unbox(v_defValue_47_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object* v_opts_54_, lean_object* v_opt_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v_opts_54_, v_opt_55_);
lean_dec_ref(v_opt_55_);
lean_dec_ref(v_opts_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(lean_object* v_mvarId_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_58_, v_x_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
v_a_74_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_65_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_65_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg___boxed(lean_object* v_mvarId_82_, lean_object* v_x_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_82_, v_x_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(lean_object* v_00_u03b1_90_, lean_object* v_mvarId_91_, lean_object* v_x_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_91_, v_x_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___boxed(lean_object* v_00_u03b1_99_, lean_object* v_mvarId_100_, lean_object* v_x_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(v_00_u03b1_99_, v_mvarId_100_, v_x_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_expr_instantiate1(v_a_108_, v_a_110_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___x_117_ = lean_infer_type(v___x_116_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_119_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v___x_119_ = l_Lean_Meta_isExprDefEq(v_a_118_, v_a_109_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
return v___x_119_;
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_a_109_);
v_a_120_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_117_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_117_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_MVarId_rewrite___lam__0(v_a_128_, v_a_129_, v_a_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec_ref(v_a_130_);
lean_dec_ref(v_a_128_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(size_t v_sz_137_, size_t v_i_138_, lean_object* v_bs_139_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = lean_usize_dec_lt(v_i_138_, v_sz_137_);
if (v___x_140_ == 0)
{
return v_bs_139_;
}
else
{
lean_object* v_v_141_; lean_object* v___x_142_; lean_object* v_bs_x27_143_; lean_object* v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
v_v_141_ = lean_array_uget(v_bs_139_, v_i_138_);
v___x_142_ = lean_unsigned_to_nat(0u);
v_bs_x27_143_ = lean_array_uset(v_bs_139_, v_i_138_, v___x_142_);
v___x_144_ = l_Lean_Expr_mvarId_x21(v_v_141_);
lean_dec(v_v_141_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_i_138_, v___x_145_);
v___x_147_ = lean_array_uset(v_bs_x27_143_, v_i_138_, v___x_144_);
v_i_138_ = v___x_146_;
v_bs_139_ = v___x_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object* v_sz_149_, lean_object* v_i_150_, lean_object* v_bs_151_){
_start:
{
size_t v_sz_boxed_152_; size_t v_i_boxed_153_; lean_object* v_res_154_; 
v_sz_boxed_152_ = lean_unbox_usize(v_sz_149_);
lean_dec(v_sz_149_);
v_i_boxed_153_ = lean_unbox_usize(v_i_150_);
lean_dec(v_i_150_);
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_boxed_152_, v_i_boxed_153_, v_bs_151_);
return v_res_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(lean_object* v_keys_155_, lean_object* v_i_156_, lean_object* v_k_157_){
_start:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_array_get_size(v_keys_155_);
v___x_159_ = lean_nat_dec_lt(v_i_156_, v___x_158_);
if (v___x_159_ == 0)
{
lean_dec(v_i_156_);
return v___x_159_;
}
else
{
lean_object* v_k_x27_160_; uint8_t v___x_161_; 
v_k_x27_160_ = lean_array_fget_borrowed(v_keys_155_, v_i_156_);
v___x_161_ = l_Lean_instBEqMVarId_beq(v_k_157_, v_k_x27_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_i_156_, v___x_162_);
lean_dec(v_i_156_);
v_i_156_ = v___x_163_;
goto _start;
}
else
{
lean_dec(v_i_156_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg___boxed(lean_object* v_keys_165_, lean_object* v_i_166_, lean_object* v_k_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_165_, v_i_166_, v_k_167_);
lean_dec(v_k_167_);
lean_dec_ref(v_keys_165_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object* v_x_170_, size_t v_x_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v_es_173_; lean_object* v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v_j_177_; lean_object* v___x_178_; 
v_es_173_ = lean_ctor_get(v_x_170_, 0);
v___x_174_ = lean_box(2);
v___x_175_ = ((size_t)31ULL);
v___x_176_ = lean_usize_land(v_x_171_, v___x_175_);
v_j_177_ = lean_usize_to_nat(v___x_176_);
v___x_178_ = lean_array_get_borrowed(v___x_174_, v_es_173_, v_j_177_);
lean_dec(v_j_177_);
switch(lean_obj_tag(v___x_178_))
{
case 0:
{
lean_object* v_key_179_; uint8_t v___x_180_; 
v_key_179_ = lean_ctor_get(v___x_178_, 0);
v___x_180_ = l_Lean_instBEqMVarId_beq(v_x_172_, v_key_179_);
return v___x_180_;
}
case 1:
{
lean_object* v_node_181_; size_t v___x_182_; size_t v___x_183_; 
v_node_181_ = lean_ctor_get(v___x_178_, 0);
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_usize_shift_right(v_x_171_, v___x_182_);
v_x_170_ = v_node_181_;
v_x_171_ = v___x_183_;
goto _start;
}
default: 
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
}
else
{
lean_object* v_ks_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_ks_186_ = lean_ctor_get(v_x_170_, 0);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_ks_186_, v___x_187_, v_x_172_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_18244__boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_x_18244__boxed_192_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_193_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_189_, v_x_18244__boxed_192_, v_x_191_);
lean_dec(v_x_191_);
lean_dec_ref(v_x_189_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
uint64_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; 
v___x_197_ = l_Lean_instHashableMVarId_hash(v_x_196_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_195_, v___x_198_, v_x_196_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_200_, v_x_201_);
lean_dec(v_x_201_);
lean_dec_ref(v_x_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object* v_mvarId_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v_mctx_208_; lean_object* v_eAssignment_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_207_ = lean_st_ref_get(v___y_205_);
v_mctx_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc_ref(v_mctx_208_);
lean_dec(v___x_207_);
v_eAssignment_209_ = lean_ctor_get(v_mctx_208_, 8);
lean_inc_ref(v_eAssignment_209_);
lean_dec_ref(v_mctx_208_);
v___x_210_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_eAssignment_209_, v_mvarId_204_);
lean_dec_ref(v_eAssignment_209_);
v___x_211_ = lean_box(v___x_210_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* v_mvarId_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec(v_mvarId_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object* v_as_217_, size_t v_i_218_, size_t v_stop_219_, lean_object* v_b_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_a_227_; uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_eq(v_i_218_, v_stop_219_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_array_uget_borrowed(v_as_217_, v_i_218_);
v___x_233_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v___x_232_, v___y_222_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; uint8_t v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = lean_unbox(v_a_234_);
lean_dec(v_a_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_inc(v___x_232_);
v___x_236_ = lean_array_push(v_b_220_, v___x_232_);
v_a_227_ = v___x_236_;
goto v___jp_226_;
}
else
{
v_a_227_ = v_b_220_;
goto v___jp_226_;
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec_ref(v_b_220_);
v_a_237_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_233_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_233_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v_b_220_);
return v___x_245_;
}
v___jp_226_:
{
size_t v___x_228_; size_t v___x_229_; 
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_218_, v___x_228_);
v_i_218_ = v___x_229_;
v_b_220_ = v_a_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_stop_248_, lean_object* v_b_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
size_t v_i_boxed_255_; size_t v_stop_boxed_256_; lean_object* v_res_257_; 
v_i_boxed_255_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_stop_boxed_256_ = lean_unbox_usize(v_stop_248_);
lean_dec(v_stop_248_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_246_, v_i_boxed_255_, v_stop_boxed_256_, v_b_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec_ref(v_as_246_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object* v_k_258_, lean_object* v_b_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; 
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
v___x_265_ = lean_apply_6(v_k_258_, v_b_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, lean_box(0));
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_k_266_, lean_object* v_b_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_266_, v_b_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object* v_name_274_, uint8_t v_bi_275_, lean_object* v_type_276_, lean_object* v_k_277_, uint8_t v_kind_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___f_284_; lean_object* v___x_285_; 
v___f_284_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_284_, 0, v_k_277_);
v___x_285_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_274_, v_bi_275_, v_type_276_, v___f_284_, v_kind_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_285_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_285_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object* v_name_302_, lean_object* v_bi_303_, lean_object* v_type_304_, lean_object* v_k_305_, lean_object* v_kind_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v_bi_boxed_312_; uint8_t v_kind_boxed_313_; lean_object* v_res_314_; 
v_bi_boxed_312_ = lean_unbox(v_bi_303_);
v_kind_boxed_313_ = lean_unbox(v_kind_306_);
v_res_314_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_302_, v_bi_boxed_312_, v_type_304_, v_k_305_, v_kind_boxed_313_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object* v_name_315_, lean_object* v_type_316_, lean_object* v_k_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
uint8_t v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = 0;
v___x_324_ = 0;
v___x_325_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_315_, v___x_323_, v_type_316_, v_k_317_, v___x_324_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object* v_name_326_, lean_object* v_type_327_, lean_object* v_k_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_326_, v_type_327_, v_k_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(lean_object* v_a_335_, lean_object* v_as_336_, size_t v_i_337_, size_t v_stop_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_usize_dec_eq(v_i_337_, v_stop_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_array_uget_borrowed(v_as_336_, v_i_337_);
v___x_341_ = l_Lean_instBEqMVarId_beq(v_a_335_, v___x_340_);
if (v___x_341_ == 0)
{
size_t v___x_342_; size_t v___x_343_; 
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_337_, v___x_342_);
v_i_337_ = v___x_343_;
goto _start;
}
else
{
return v___x_341_;
}
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6___boxed(lean_object* v_a_346_, lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_){
_start:
{
size_t v_i_boxed_350_; size_t v_stop_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_i_boxed_350_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_346_, v_as_347_, v_i_boxed_350_, v_stop_boxed_351_);
lean_dec_ref(v_as_347_);
lean_dec(v_a_346_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object* v_as_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_array_get_size(v_as_354_);
v___x_358_ = lean_nat_dec_lt(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
return v___x_358_;
}
else
{
size_t v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = ((size_t)0ULL);
v___x_360_ = lean_usize_of_nat(v___x_357_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_355_, v_as_354_, v___x_359_, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* v_as_362_, lean_object* v_a_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_as_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object* v_a_366_, lean_object* v_as_367_, size_t v_i_368_, size_t v_stop_369_, lean_object* v_b_370_){
_start:
{
lean_object* v___y_372_; uint8_t v___x_376_; 
v___x_376_ = lean_usize_dec_eq(v_i_368_, v_stop_369_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = lean_array_uget_borrowed(v_as_367_, v_i_368_);
v___x_378_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_a_366_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_inc(v___x_377_);
v___x_379_ = lean_array_push(v_b_370_, v___x_377_);
v___y_372_ = v___x_379_;
goto v___jp_371_;
}
else
{
v___y_372_ = v_b_370_;
goto v___jp_371_;
}
}
else
{
return v_b_370_;
}
v___jp_371_:
{
size_t v___x_373_; size_t v___x_374_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_368_, v___x_373_);
v_i_368_ = v___x_374_;
v_b_370_ = v___y_372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* v_a_380_, lean_object* v_as_381_, lean_object* v_i_382_, lean_object* v_stop_383_, lean_object* v_b_384_){
_start:
{
size_t v_i_boxed_385_; size_t v_stop_boxed_386_; lean_object* v_res_387_; 
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_stop_boxed_386_ = lean_unbox_usize(v_stop_383_);
lean_dec(v_stop_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_380_, v_as_381_, v_i_boxed_385_, v_stop_boxed_386_, v_b_384_);
lean_dec_ref(v_as_381_);
lean_dec_ref(v_a_380_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(lean_object* v_msgData_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_env_395_; uint8_t v___x_396_; lean_object* v_env_397_; lean_object* v___x_398_; lean_object* v_toCold_399_; lean_object* v_mctx_400_; lean_object* v_lctx_401_; lean_object* v_options_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_394_ = lean_st_ref_get(v___y_392_);
v_env_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_env_395_);
lean_dec(v___x_394_);
v___x_396_ = 0;
v_env_397_ = l_Lean_Environment_setRecordingDeps(v_env_395_, v___x_396_);
v___x_398_ = lean_st_ref_get(v___y_390_);
v_toCold_399_ = lean_ctor_get(v___y_391_, 0);
v_mctx_400_ = lean_ctor_get(v___x_398_, 0);
lean_inc_ref(v_mctx_400_);
lean_dec(v___x_398_);
v_lctx_401_ = lean_ctor_get(v___y_389_, 2);
v_options_402_ = lean_ctor_get(v_toCold_399_, 2);
lean_inc_ref(v_options_402_);
lean_inc_ref(v_lctx_401_);
v___x_403_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_403_, 0, v_env_397_);
lean_ctor_set(v___x_403_, 1, v_mctx_400_);
lean_ctor_set(v___x_403_, 2, v_lctx_401_);
lean_ctor_set(v___x_403_, 3, v_options_402_);
v___x_404_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_msgData_388_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(lean_object* v_msgData_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_ref_419_; lean_object* v___x_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_ref_419_ = lean_ctor_get(v___y_416_, 2);
v___x_420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_ref_419_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_ref_419_);
lean_ctor_set(v___x_425_, 1, v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__0));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__2));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__7));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__9));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__11));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__15));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__17));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__19));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__22(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__21));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__27(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__26));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__31(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__30));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__32));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__34));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__36));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__38));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__46(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_box(0);
v___x_507_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__45));
v___x_508_ = l_Lean_mkConst(v___x_507_, v___x_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* v_mvarId_509_, lean_object* v___x_510_, lean_object* v_heq_511_, lean_object* v_e_512_, lean_object* v_config_513_, uint8_t v_symm_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___x_548_; 
lean_inc(v___x_510_);
lean_inc(v_mvarId_509_);
v___x_548_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_509_, v___x_510_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v___x_549_; 
lean_dec_ref_known(v___x_548_, 1);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc_ref(v_heq_511_);
v___x_549_ = lean_infer_type(v_heq_511_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_1060_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_a_550_, v___y_516_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_1060_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_1060_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(0);
v___x_557_ = 0;
v___x_558_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_552_, v___x_556_, v___x_557_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v_snd_560_; lean_object* v_fst_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_1051_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v_snd_560_ = lean_ctor_get(v_a_559_, 1);
v_fst_561_ = lean_ctor_get(v_a_559_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_563_ = v_a_559_;
v_isShared_564_ = v_isSharedCheck_1051_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snd_560_);
lean_inc(v_fst_561_);
lean_dec(v_a_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_1051_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_1050_; 
v_fst_565_ = lean_ctor_get(v_snd_560_, 0);
v_snd_566_ = lean_ctor_get(v_snd_560_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_568_ = v_snd_560_;
v_isShared_569_ = v_isSharedCheck_1050_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v_snd_560_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_1050_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; size_t v___y_578_; lean_object* v_a_579_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v_eNew_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_946_; lean_object* v_heq_947_; lean_object* v_heqType_948_; lean_object* v_lhs_949_; lean_object* v_rhs_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v_heq_974_; lean_object* v_heqType_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
lean_inc_ref(v_heq_511_);
v___x_1031_ = l_Lean_mkAppN(v_heq_511_, v_fst_561_);
v___x_1032_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__43));
v___x_1033_ = lean_unsigned_to_nat(2u);
v___x_1034_ = l_Lean_Expr_isAppOfArity(v_snd_566_, v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
v_heq_974_ = v___x_1031_;
v_heqType_975_ = v_snd_566_;
v___y_976_ = v___y_515_;
v___y_977_ = v___y_516_;
v___y_978_ = v___y_517_;
v___y_979_ = v___y_518_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = l_Lean_Expr_appFn_x21(v_snd_566_);
v___x_1036_ = l_Lean_Expr_appArg_x21(v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = l_Lean_Expr_appArg_x21(v_snd_566_);
lean_dec(v_snd_566_);
lean_inc_ref(v___x_1037_);
lean_inc_ref(v___x_1036_);
v___x_1038_ = l_Lean_Meta_mkEq(v___x_1036_, v___x_1037_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__46, &l_Lean_MVarId_rewrite___lam__1___closed__46_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__46);
v___x_1041_ = l_Lean_mkApp3(v___x_1040_, v___x_1036_, v___x_1037_, v___x_1031_);
v_heq_974_ = v___x_1041_;
v_heqType_975_ = v_a_1039_;
v___y_976_ = v___y_515_;
v___y_977_ = v___y_516_;
v___y_978_ = v___y_517_;
v___y_979_ = v___y_518_;
goto v___jp_973_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___x_1037_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v___x_1031_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1042_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1038_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_appendParentTag(v_mvarId_509_, v_fst_561_, v_fst_565_, v___y_575_, v___y_571_, v___y_572_, v___y_574_);
lean_dec(v_fst_565_);
lean_dec(v_fst_561_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; 
lean_dec_ref_known(v___x_580_, 1);
v___x_581_ = l_Lean_Meta_getMVarsNoDelayed(v_heq_511_, v___y_575_, v___y_571_, v___y_572_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_575_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = lean_array_get_size(v_a_582_);
v___x_584_ = lean_mk_empty_array_with_capacity(v___y_573_);
v___x_585_ = lean_nat_dec_lt(v___y_573_, v___x_583_);
if (v___x_585_ == 0)
{
lean_dec(v_a_582_);
v___y_540_ = v_a_579_;
v___y_541_ = v___y_576_;
v___y_542_ = v___y_577_;
v___y_543_ = v___x_584_;
goto v___jp_539_;
}
else
{
size_t v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_usize_of_nat(v___x_583_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_579_, v_a_582_, v___y_578_, v___x_586_, v___x_584_);
lean_dec(v_a_582_);
v___y_540_ = v_a_579_;
v___y_541_ = v___y_576_;
v___y_542_ = v___y_577_;
v___y_543_ = v___x_587_;
goto v___jp_539_;
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_a_579_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
v_a_588_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_581_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_581_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_a_579_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v_heq_511_);
v_a_596_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_580_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_580_);
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
v___jp_604_:
{
uint8_t v___x_612_; lean_object* v___x_613_; 
v___x_612_ = 0;
lean_inc(v_fst_565_);
lean_inc(v_mvarId_509_);
v___x_613_ = l_Lean_Meta_postprocessAppMVars(v___x_510_, v_mvarId_509_, v_fst_561_, v_fst_565_, v___y_611_, v___x_612_, v___y_608_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_613_) == 0)
{
size_t v_sz_614_; size_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
lean_dec_ref_known(v___x_613_, 1);
v_sz_614_ = lean_array_size(v_fst_561_);
v___x_615_ = ((size_t)0ULL);
lean_inc(v_fst_561_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_614_, v___x_615_, v_fst_561_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_array_get_size(v___x_616_);
v___x_619_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__4));
v___x_620_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_616_);
v___y_571_ = v___y_605_;
v___y_572_ = v___y_606_;
v___y_573_ = v___x_617_;
v___y_574_ = v___y_607_;
v___y_575_ = v___y_608_;
v___y_576_ = v___y_609_;
v___y_577_ = v___y_610_;
v___y_578_ = v___x_615_;
v_a_579_ = v___x_619_;
goto v___jp_570_;
}
else
{
size_t v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_usize_of_nat(v___x_618_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_616_, v___x_615_, v___x_621_, v___x_619_, v___y_608_, v___y_605_, v___y_606_, v___y_607_);
lean_dec_ref(v___x_616_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___y_571_ = v___y_605_;
v___y_572_ = v___y_606_;
v___y_573_ = v___x_617_;
v___y_574_ = v___y_607_;
v___y_575_ = v___y_608_;
v___y_576_ = v___y_609_;
v___y_577_ = v___y_610_;
v___y_578_ = v___x_615_;
v_a_579_ = v_a_623_;
goto v___jp_570_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v_fst_565_);
lean_dec(v_fst_561_);
lean_dec_ref(v_heq_511_);
lean_dec(v_mvarId_509_);
v_a_624_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_622_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_622_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v_fst_565_);
lean_dec(v_fst_561_);
lean_dec_ref(v_heq_511_);
lean_dec(v_mvarId_509_);
v_a_632_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_613_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_613_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
v___jp_640_:
{
lean_object* v___x_652_; 
lean_inc_ref(v___y_643_);
v___x_652_ = l_Lean_Meta_getLevel(v___y_643_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
lean_inc_ref(v___y_646_);
v___x_654_ = l_Lean_Meta_getLevel(v___y_646_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_657_ = lean_box(0);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 1);
lean_ctor_set(v___x_568_, 1, v___x_657_);
lean_ctor_set(v___x_568_, 0, v_a_655_);
v___x_659_ = v___x_568_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_670_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 1);
lean_ctor_set(v___x_563_, 1, v___x_659_);
lean_ctor_set(v___x_563_, 0, v_a_653_);
v___x_661_ = v___x_563_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_653_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_669_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_662_ = l_Lean_Expr_const___override(v___x_656_, v___x_661_);
v___x_663_ = l_Lean_mkApp6(v___x_662_, v___y_643_, v___y_646_, v___y_641_, v___y_642_, v___y_644_, v___y_645_);
v___x_664_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_650_);
v___x_665_ = l_Lean_Meta_tactic_skipAssignedInstances;
v___x_666_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v___x_664_, v___x_665_);
lean_dec_ref(v___x_664_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
v___x_667_ = 1;
v___y_605_ = v___y_649_;
v___y_606_ = v___y_650_;
v___y_607_ = v___y_651_;
v___y_608_ = v___y_648_;
v___y_609_ = v___x_663_;
v___y_610_ = v___y_647_;
v___y_611_ = v___x_667_;
goto v___jp_604_;
}
else
{
uint8_t v___x_668_; 
v___x_668_ = 0;
v___y_605_ = v___y_649_;
v___y_606_ = v___y_650_;
v___y_607_ = v___y_651_;
v___y_608_ = v___y_648_;
v___y_609_ = v___x_663_;
v___y_610_ = v___y_647_;
v___y_611_ = v___x_668_;
goto v___jp_604_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_a_653_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v___y_641_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_671_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_654_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_654_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v___y_641_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_679_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_652_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_652_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
v___jp_687_:
{
lean_object* v___x_702_; 
lean_inc_ref(v___y_688_);
v___x_702_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v___y_690_, v___y_688_, v___y_689_, v___y_695_, v___y_700_, v___y_696_, v___y_691_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; uint8_t v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_705_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__8, &l_Lean_MVarId_rewrite___lam__1___closed__8_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__8);
lean_inc_ref(v___y_692_);
v___x_706_ = l_Lean_MessageData_ofExpr(v___y_692_);
v___x_707_ = l_Lean_indentD(v___x_706_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_705_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__10, &l_Lean_MVarId_rewrite___lam__1___closed__10_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__10);
v___x_710_ = l_Lean_indentExpr(v___y_693_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__12, &l_Lean_MVarId_rewrite___lam__1___closed__12_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__12);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
lean_inc_ref(v___y_697_);
v___x_714_ = l_Lean_indentExpr(v___y_697_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l_Lean_MessageData_note(v___x_715_);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_708_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 0, v___x_717_);
v___x_719_ = v___x_554_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_729_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
lean_inc(v_mvarId_509_);
lean_inc(v___x_510_);
v___x_720_ = l_Lean_Meta_throwTacticEx___redArg(v___x_510_, v_mvarId_509_, v___x_719_, v___y_695_, v___y_700_, v___y_696_, v___y_691_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref_known(v___x_720_, 1);
v___y_641_ = v___y_697_;
v___y_642_ = v___y_698_;
v___y_643_ = v___y_688_;
v___y_644_ = v___y_692_;
v___y_645_ = v___y_699_;
v___y_646_ = v___y_694_;
v___y_647_ = v___y_701_;
v___y_648_ = v___y_695_;
v___y_649_ = v___y_700_;
v___y_650_ = v___y_696_;
v___y_651_ = v___y_691_;
goto v___jp_640_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_688_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_693_);
lean_del_object(v___x_554_);
v___y_641_ = v___y_697_;
v___y_642_ = v___y_698_;
v___y_643_ = v___y_688_;
v___y_644_ = v___y_692_;
v___y_645_ = v___y_699_;
v___y_646_ = v___y_694_;
v___y_647_ = v___y_701_;
v___y_648_ = v___y_695_;
v___y_649_ = v___y_700_;
v___y_650_ = v___y_696_;
v___y_651_ = v___y_691_;
goto v___jp_640_;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_688_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_730_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_702_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_702_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
v___jp_738_:
{
lean_object* v___x_751_; 
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc_ref(v___y_744_);
v___x_751_ = lean_infer_type(v___y_744_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___f_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_n(v_a_752_, 2);
lean_dec_ref_known(v___x_751_, 1);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(v___f_753_, 0, v___y_739_);
lean_closure_set(v___f_753_, 1, v_a_752_);
v___x_754_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__14));
v___x_755_ = 0;
lean_inc_ref(v___y_743_);
v___x_756_ = l_Lean_mkLambda(v___x_754_, v___x_755_, v___y_743_, v___y_741_);
v___x_757_ = 0;
lean_inc_ref(v___x_756_);
v___x_758_ = l_Lean_Meta_check(v___x_756_, v___x_757_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref_known(v___x_758_, 1);
v___y_688_ = v___y_743_;
v___y_689_ = v___f_753_;
v___y_690_ = v___x_754_;
v___y_691_ = v___y_750_;
v___y_692_ = v___x_756_;
v___y_693_ = v___y_744_;
v___y_694_ = v_a_752_;
v___y_695_ = v___y_747_;
v___y_696_ = v___y_749_;
v___y_697_ = v___y_740_;
v___y_698_ = v___y_742_;
v___y_699_ = v___y_745_;
v___y_700_ = v___y_748_;
v___y_701_ = v_eNew_746_;
goto v___jp_687_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_806_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_806_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_806_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_806_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = l_Lean_Exception_isInterrupt(v_a_759_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; 
lean_inc(v_a_759_);
v___x_764_ = l_Lean_Exception_isRuntime(v_a_759_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_del_object(v___x_761_);
v___x_765_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__16, &l_Lean_MVarId_rewrite___lam__1___closed__16_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__16);
lean_inc_ref(v___x_756_);
v___x_766_ = l_Lean_MessageData_ofExpr(v___x_756_);
v___x_767_ = l_Lean_indentD(v___x_766_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_765_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__18, &l_Lean_MVarId_rewrite___lam__1___closed__18_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__18);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l_Lean_Exception_toMessageData(v_a_759_);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__20, &l_Lean_MVarId_rewrite___lam__1___closed__20_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__20);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_776_ = l_Lean_MessageData_ofConstName(v___x_775_, v___x_764_);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__22, &l_Lean_MVarId_rewrite___lam__1___closed__22_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__22);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__25));
v___x_781_ = l_Lean_MessageData_ofConstName(v___x_780_, v___x_764_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__27, &l_Lean_MVarId_rewrite___lam__1___closed__27_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__27);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__29));
v___x_786_ = l_Lean_MessageData_ofConstName(v___x_785_, v___x_764_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_784_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__31, &l_Lean_MVarId_rewrite___lam__1___closed__31_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__31);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_inc(v_mvarId_509_);
lean_inc(v___x_510_);
v___x_791_ = l_Lean_Meta_throwTacticEx___redArg(v___x_510_, v_mvarId_509_, v___x_790_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_dec_ref_known(v___x_791_, 1);
v___y_688_ = v___y_743_;
v___y_689_ = v___f_753_;
v___y_690_ = v___x_754_;
v___y_691_ = v___y_750_;
v___y_692_ = v___x_756_;
v___y_693_ = v___y_744_;
v___y_694_ = v_a_752_;
v___y_695_ = v___y_747_;
v___y_696_ = v___y_749_;
v___y_697_ = v___y_740_;
v___y_698_ = v___y_742_;
v___y_699_ = v___y_745_;
v___y_700_ = v___y_748_;
v___y_701_ = v_eNew_746_;
goto v___jp_687_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v___x_756_);
lean_dec_ref(v___f_753_);
lean_dec(v_a_752_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_eNew_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_740_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v___x_801_; 
lean_dec_ref(v___x_756_);
lean_dec_ref(v___f_753_);
lean_dec(v_a_752_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_eNew_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_740_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
if (v_isShared_762_ == 0)
{
v___x_801_ = v___x_761_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_759_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v___x_804_; 
lean_dec_ref(v___x_756_);
lean_dec_ref(v___f_753_);
lean_dec(v_a_752_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_eNew_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_740_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
if (v_isShared_762_ == 0)
{
v___x_804_ = v___x_761_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_759_);
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
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_eNew_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec_ref(v___y_739_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_807_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_751_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_751_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
v___jp_815_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_a_828_; uint8_t v___x_829_; 
v___x_826_ = lean_expr_instantiate1(v___y_816_, v___y_819_);
v___x_827_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v___x_826_, v___y_823_);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Lean_Expr_hasBinderNameHint(v___y_819_);
if (v___x_829_ == 0)
{
lean_inc_ref(v___y_816_);
v___y_739_ = v___y_816_;
v___y_740_ = v___y_817_;
v___y_741_ = v___y_816_;
v___y_742_ = v___y_819_;
v___y_743_ = v___y_818_;
v___y_744_ = v___y_820_;
v___y_745_ = v___y_821_;
v_eNew_746_ = v_a_828_;
v___y_747_ = v___y_822_;
v___y_748_ = v___y_823_;
v___y_749_ = v___y_824_;
v___y_750_ = v___y_825_;
goto v___jp_738_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Expr_resolveBinderNameHint(v_a_828_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
lean_inc_ref(v___y_816_);
v___y_739_ = v___y_816_;
v___y_740_ = v___y_817_;
v___y_741_ = v___y_816_;
v___y_742_ = v___y_819_;
v___y_743_ = v___y_818_;
v___y_744_ = v___y_820_;
v___y_745_ = v___y_821_;
v_eNew_746_ = v_a_831_;
v___y_747_ = v___y_822_;
v___y_748_ = v___y_823_;
v___y_749_ = v___y_824_;
v___y_750_ = v___y_825_;
goto v___jp_738_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec_ref(v___y_816_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_832_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_830_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
v___jp_840_:
{
lean_object* v___x_849_; lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_944_; 
v___x_849_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_512_, v___y_846_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_944_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_944_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_944_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v_transparency_854_; uint8_t v_offsetCnstrs_855_; lean_object* v_occs_856_; lean_object* v___x_857_; uint8_t v_foApprox_858_; uint8_t v_ctxApprox_859_; uint8_t v_quasiPatternApprox_860_; uint8_t v_constApprox_861_; uint8_t v_isDefEqStuckEx_862_; uint8_t v_unificationHints_863_; uint8_t v_proofIrrelevance_864_; uint8_t v_assignSyntheticOpaque_865_; uint8_t v_etaStruct_866_; uint8_t v_univApprox_867_; uint8_t v_iota_868_; uint8_t v_beta_869_; uint8_t v_proj_870_; uint8_t v_zeta_871_; uint8_t v_zetaDelta_872_; uint8_t v_zetaUnused_873_; uint8_t v_zetaHave_874_; uint8_t v_canUnfoldPredicateConfig_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_943_; 
v_transparency_854_ = lean_ctor_get_uint8(v_config_513_, sizeof(void*)*1);
v_offsetCnstrs_855_ = lean_ctor_get_uint8(v_config_513_, sizeof(void*)*1 + 1);
v_occs_856_ = lean_ctor_get(v_config_513_, 0);
lean_inc(v_occs_856_);
lean_dec_ref(v_config_513_);
v___x_857_ = l_Lean_Meta_Context_config(v___y_845_);
v_foApprox_858_ = lean_ctor_get_uint8(v___x_857_, 0);
v_ctxApprox_859_ = lean_ctor_get_uint8(v___x_857_, 1);
v_quasiPatternApprox_860_ = lean_ctor_get_uint8(v___x_857_, 2);
v_constApprox_861_ = lean_ctor_get_uint8(v___x_857_, 3);
v_isDefEqStuckEx_862_ = lean_ctor_get_uint8(v___x_857_, 4);
v_unificationHints_863_ = lean_ctor_get_uint8(v___x_857_, 5);
v_proofIrrelevance_864_ = lean_ctor_get_uint8(v___x_857_, 6);
v_assignSyntheticOpaque_865_ = lean_ctor_get_uint8(v___x_857_, 7);
v_etaStruct_866_ = lean_ctor_get_uint8(v___x_857_, 10);
v_univApprox_867_ = lean_ctor_get_uint8(v___x_857_, 11);
v_iota_868_ = lean_ctor_get_uint8(v___x_857_, 12);
v_beta_869_ = lean_ctor_get_uint8(v___x_857_, 13);
v_proj_870_ = lean_ctor_get_uint8(v___x_857_, 14);
v_zeta_871_ = lean_ctor_get_uint8(v___x_857_, 15);
v_zetaDelta_872_ = lean_ctor_get_uint8(v___x_857_, 16);
v_zetaUnused_873_ = lean_ctor_get_uint8(v___x_857_, 17);
v_zetaHave_874_ = lean_ctor_get_uint8(v___x_857_, 18);
v_canUnfoldPredicateConfig_875_ = lean_ctor_get_uint8(v___x_857_, 19);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_943_ == 0)
{
v___x_877_ = v___x_857_;
v_isShared_878_ = v_isSharedCheck_943_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_857_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_943_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v_trackZetaDelta_879_; lean_object* v_zetaDeltaSet_880_; lean_object* v_lctx_881_; lean_object* v_localInstances_882_; lean_object* v_defEqCtx_x3f_883_; lean_object* v_synthPendingDepth_884_; lean_object* v_customCanUnfoldPredicate_x3f_885_; uint8_t v_univApprox_886_; uint8_t v_inTypeClassResolution_887_; uint8_t v_cacheInferType_888_; lean_object* v___x_890_; 
v_trackZetaDelta_879_ = lean_ctor_get_uint8(v___y_845_, sizeof(void*)*7);
v_zetaDeltaSet_880_ = lean_ctor_get(v___y_845_, 1);
v_lctx_881_ = lean_ctor_get(v___y_845_, 2);
v_localInstances_882_ = lean_ctor_get(v___y_845_, 3);
v_defEqCtx_x3f_883_ = lean_ctor_get(v___y_845_, 4);
v_synthPendingDepth_884_ = lean_ctor_get(v___y_845_, 5);
v_customCanUnfoldPredicate_x3f_885_ = lean_ctor_get(v___y_845_, 6);
v_univApprox_886_ = lean_ctor_get_uint8(v___y_845_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_887_ = lean_ctor_get_uint8(v___y_845_, sizeof(void*)*7 + 2);
v_cacheInferType_888_ = lean_ctor_get_uint8(v___y_845_, sizeof(void*)*7 + 3);
if (v_isShared_878_ == 0)
{
v___x_890_ = v___x_877_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 0, v_foApprox_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 1, v_ctxApprox_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 2, v_quasiPatternApprox_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 3, v_constApprox_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 4, v_isDefEqStuckEx_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 5, v_unificationHints_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 6, v_proofIrrelevance_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 7, v_assignSyntheticOpaque_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 10, v_etaStruct_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 11, v_univApprox_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 12, v_iota_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 13, v_beta_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 14, v_proj_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 15, v_zeta_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 16, v_zetaDelta_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 17, v_zetaUnused_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 18, v_zetaHave_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 19, v_canUnfoldPredicateConfig_875_);
v___x_890_ = v_reuseFailAlloc_942_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
uint64_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_ctor_set_uint8(v___x_890_, 8, v_offsetCnstrs_855_);
lean_ctor_set_uint8(v___x_890_, 9, v_transparency_854_);
v___x_891_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set_uint64(v___x_892_, sizeof(void*)*1, v___x_891_);
lean_inc(v_customCanUnfoldPredicate_x3f_885_);
lean_inc(v_synthPendingDepth_884_);
lean_inc(v_defEqCtx_x3f_883_);
lean_inc_ref(v_localInstances_882_);
lean_inc_ref(v_lctx_881_);
lean_inc(v_zetaDeltaSet_880_);
v___x_893_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_zetaDeltaSet_880_);
lean_ctor_set(v___x_893_, 2, v_lctx_881_);
lean_ctor_set(v___x_893_, 3, v_localInstances_882_);
lean_ctor_set(v___x_893_, 4, v_defEqCtx_x3f_883_);
lean_ctor_set(v___x_893_, 5, v_synthPendingDepth_884_);
lean_ctor_set(v___x_893_, 6, v_customCanUnfoldPredicate_x3f_885_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7, v_trackZetaDelta_879_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7 + 1, v_univApprox_886_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7 + 2, v_inTypeClassResolution_887_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*7 + 3, v_cacheInferType_888_);
lean_inc_ref(v___y_841_);
lean_inc(v_a_850_);
v___x_894_ = l_Lean_Meta_kabstract(v_a_850_, v___y_841_, v_occs_856_, v___x_893_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; uint8_t v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = l_Lean_Expr_hasLooseBVars(v_a_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_inc_ref(v___y_841_);
lean_inc(v_a_850_);
v___x_897_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_850_, v___y_841_, v___x_893_, v___y_846_, v___y_847_, v___y_848_);
lean_dec_ref_known(v___x_893_, 7);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_925_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v_fst_899_ = lean_ctor_get(v_a_898_, 0);
v_snd_900_ = lean_ctor_get(v_a_898_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_a_898_);
if (v_isSharedCheck_925_ == 0)
{
v___x_902_ = v_a_898_;
v_isShared_903_ = v_isSharedCheck_925_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snd_900_);
lean_inc(v_fst_899_);
lean_dec(v_a_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_925_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_904_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__33, &l_Lean_MVarId_rewrite___lam__1___closed__33_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__33);
v___x_905_ = l_Lean_indentExpr(v_snd_900_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 7);
lean_ctor_set(v___x_902_, 1, v___x_905_);
lean_ctor_set(v___x_902_, 0, v___x_904_);
v___x_907_ = v___x_902_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_905_);
v___x_907_ = v_reuseFailAlloc_924_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_908_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__35, &l_Lean_MVarId_rewrite___lam__1___closed__35_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__35);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_indentExpr(v_fst_899_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 1);
lean_ctor_set(v___x_852_, 0, v___x_911_);
v___x_913_ = v___x_852_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_923_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; 
lean_inc(v_mvarId_509_);
lean_inc(v___x_510_);
v___x_914_ = l_Lean_Meta_throwTacticEx___redArg(v___x_510_, v_mvarId_509_, v___x_913_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_dec_ref_known(v___x_914_, 1);
v___y_816_ = v_a_895_;
v___y_817_ = v___y_841_;
v___y_818_ = v___y_842_;
v___y_819_ = v___y_843_;
v___y_820_ = v_a_850_;
v___y_821_ = v___y_844_;
v___y_822_ = v___y_845_;
v___y_823_ = v___y_846_;
v___y_824_ = v___y_847_;
v___y_825_ = v___y_848_;
goto v___jp_815_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_a_895_);
lean_dec(v_a_850_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_895_);
lean_del_object(v___x_852_);
lean_dec(v_a_850_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_926_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_897_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_897_);
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
else
{
lean_dec_ref_known(v___x_893_, 7);
lean_del_object(v___x_852_);
v___y_816_ = v_a_895_;
v___y_817_ = v___y_841_;
v___y_818_ = v___y_842_;
v___y_819_ = v___y_843_;
v___y_820_ = v_a_850_;
v___y_821_ = v___y_844_;
v___y_822_ = v___y_845_;
v___y_823_ = v___y_846_;
v___y_824_ = v___y_847_;
v___y_825_ = v___y_848_;
goto v___jp_815_;
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref_known(v___x_893_, 7);
lean_del_object(v___x_852_);
lean_dec(v_a_850_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_934_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_894_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_894_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
v___jp_945_:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = l_Lean_Expr_getAppFn(v_lhs_949_);
v___x_956_ = l_Lean_Expr_isMVar(v___x_955_);
lean_dec_ref(v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_heqType_948_);
v___y_841_ = v_lhs_949_;
v___y_842_ = v___y_946_;
v___y_843_ = v_rhs_950_;
v___y_844_ = v_heq_947_;
v___y_845_ = v___y_951_;
v___y_846_ = v___y_952_;
v___y_847_ = v___y_953_;
v___y_848_ = v___y_954_;
goto v___jp_840_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_rhs_950_);
lean_dec_ref(v_heq_947_);
lean_dec_ref(v___y_946_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v___x_957_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__37, &l_Lean_MVarId_rewrite___lam__1___closed__37_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__37);
v___x_958_ = l_Lean_MessageData_ofExpr(v_lhs_949_);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__39, &l_Lean_MVarId_rewrite___lam__1___closed__39_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__39);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Lean_indentExpr(v_heqType_948_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_963_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
v___jp_973_:
{
lean_object* v___x_980_; 
lean_inc_ref(v_heqType_975_);
v___x_980_ = l_Lean_Meta_matchEq_x3f(v_heqType_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
if (lean_obj_tag(v_a_981_) == 0)
{
lean_object* v___x_982_; 
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
lean_inc_ref(v_heqType_975_);
v___x_982_ = l_Lean_Meta_isProp(v_heqType_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; uint8_t v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = lean_unbox(v_a_983_);
lean_dec(v_a_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__40));
v___y_521_ = v___y_979_;
v___y_522_ = v___y_976_;
v___y_523_ = v_heqType_975_;
v___y_524_ = v___y_978_;
v___y_525_ = v___y_977_;
v___y_526_ = v_heq_974_;
v___y_527_ = v___x_985_;
goto v___jp_520_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__41));
v___y_521_ = v___y_979_;
v___y_522_ = v___y_976_;
v___y_523_ = v_heqType_975_;
v___y_524_ = v___y_978_;
v___y_525_ = v___y_977_;
v___y_526_ = v_heq_974_;
v___y_527_ = v___x_986_;
goto v___jp_520_;
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_heqType_975_);
lean_dec_ref(v_heq_974_);
v_a_987_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_982_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_982_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_val_995_; lean_object* v_snd_996_; 
v_val_995_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_a_981_, 1);
v_snd_996_ = lean_ctor_get(v_val_995_, 1);
lean_inc(v_snd_996_);
if (v_symm_514_ == 0)
{
lean_object* v_fst_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; 
v_fst_997_ = lean_ctor_get(v_val_995_, 0);
lean_inc(v_fst_997_);
lean_dec(v_val_995_);
v_fst_998_ = lean_ctor_get(v_snd_996_, 0);
lean_inc(v_fst_998_);
v_snd_999_ = lean_ctor_get(v_snd_996_, 1);
lean_inc(v_snd_999_);
lean_dec(v_snd_996_);
v___y_946_ = v_fst_997_;
v_heq_947_ = v_heq_974_;
v_heqType_948_ = v_heqType_975_;
v_lhs_949_ = v_fst_998_;
v_rhs_950_ = v_snd_999_;
v___y_951_ = v___y_976_;
v___y_952_ = v___y_977_;
v___y_953_ = v___y_978_;
v___y_954_ = v___y_979_;
goto v___jp_945_;
}
else
{
lean_object* v_fst_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v_heqType_975_);
v_fst_1000_ = lean_ctor_get(v_val_995_, 0);
lean_inc(v_fst_1000_);
lean_dec(v_val_995_);
v_fst_1001_ = lean_ctor_get(v_snd_996_, 0);
lean_inc(v_fst_1001_);
v_snd_1002_ = lean_ctor_get(v_snd_996_, 1);
lean_inc(v_snd_1002_);
lean_dec(v_snd_996_);
v___x_1003_ = l_Lean_Meta_mkEqSymm(v_heq_974_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
lean_inc(v_fst_1001_);
lean_inc(v_snd_1002_);
v___x_1005_ = l_Lean_Meta_mkEq(v_snd_1002_, v_fst_1001_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___y_946_ = v_fst_1000_;
v_heq_947_ = v_a_1004_;
v_heqType_948_ = v_a_1006_;
v_lhs_949_ = v_snd_1002_;
v_rhs_950_ = v_fst_1001_;
v___y_951_ = v___y_976_;
v___y_952_ = v___y_977_;
v___y_953_ = v___y_978_;
v___y_954_ = v___y_979_;
goto v___jp_945_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_1004_);
lean_dec(v_snd_1002_);
lean_dec(v_fst_1001_);
lean_dec(v_fst_1000_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1007_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_snd_1002_);
lean_dec(v_fst_1001_);
lean_dec(v_fst_1000_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1015_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1003_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1003_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_heqType_975_);
lean_dec_ref(v_heq_974_);
lean_del_object(v___x_568_);
lean_dec(v_fst_565_);
lean_del_object(v___x_563_);
lean_dec(v_fst_561_);
lean_del_object(v___x_554_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1023_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_980_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_980_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_554_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1052_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_558_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_558_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1061_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_549_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_549_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_config_513_);
lean_dec_ref(v_e_512_);
lean_dec_ref(v_heq_511_);
lean_dec(v___x_510_);
lean_dec(v_mvarId_509_);
v_a_1069_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_548_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_548_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
v___jp_520_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_528_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__1, &l_Lean_MVarId_rewrite___lam__1___closed__1_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__1);
v___x_529_ = lean_unsigned_to_nat(30u);
v___x_530_ = l_Lean_inlineExpr(v___y_526_, v___x_529_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__3, &l_Lean_MVarId_rewrite___lam__1___closed__3_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__3);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_inc_ref(v___y_527_);
v___x_534_ = l_Lean_stringToMessageData(v___y_527_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_indentExpr(v___y_523_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_537_, v___y_522_, v___y_525_, v___y_524_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_522_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = l_Array_append___redArg(v___y_540_, v___y_543_);
lean_dec_ref(v___y_543_);
v___x_545_ = lean_array_to_list(v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_546_, 0, v___y_542_);
lean_ctor_set(v___x_546_, 1, v___y_541_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* v_mvarId_1077_, lean_object* v___x_1078_, lean_object* v_heq_1079_, lean_object* v_e_1080_, lean_object* v_config_1081_, lean_object* v_symm_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v_symm_boxed_1088_; lean_object* v_res_1089_; 
v_symm_boxed_1088_ = lean_unbox(v_symm_1082_);
v_res_1089_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_1077_, v___x_1078_, v_heq_1079_, v_e_1080_, v_config_1081_, v_symm_boxed_1088_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* v_mvarId_1093_, lean_object* v_e_1094_, lean_object* v_heq_1095_, uint8_t v_symm_1096_, lean_object* v_config_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v___x_1103_ = ((lean_object*)(l_Lean_MVarId_rewrite___closed__1));
v___x_1104_ = lean_box(v_symm_1096_);
lean_inc(v_mvarId_1093_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1105_, 0, v_mvarId_1093_);
lean_closure_set(v___f_1105_, 1, v___x_1103_);
lean_closure_set(v___f_1105_, 2, v_heq_1095_);
lean_closure_set(v___f_1105_, 3, v_e_1094_);
lean_closure_set(v___f_1105_, 4, v_config_1097_);
lean_closure_set(v___f_1105_, 5, v___x_1104_);
v___x_1106_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_1093_, v___f_1105_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* v_mvarId_1107_, lean_object* v_e_1108_, lean_object* v_heq_1109_, lean_object* v_symm_1110_, lean_object* v_config_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v_symm_boxed_1117_; lean_object* v_res_1118_; 
v_symm_boxed_1117_ = lean_unbox(v_symm_1110_);
v_res_1118_ = l_Lean_MVarId_rewrite(v_mvarId_1107_, v_e_1108_, v_heq_1109_, v_symm_boxed_1117_, v_config_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* v_mvarId_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_1119_, v___y_1121_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* v_mvarId_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v_mvarId_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object* v_00_u03b1_1133_, lean_object* v_msg_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(v_00_u03b1_1141_, v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_object* v_00_u03b1_1149_, lean_object* v_name_1150_, uint8_t v_bi_1151_, lean_object* v_type_1152_, lean_object* v_k_1153_, uint8_t v_kind_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1150_, v_bi_1151_, v_type_1152_, v_k_1153_, v_kind_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_name_1162_, lean_object* v_bi_1163_, lean_object* v_type_1164_, lean_object* v_k_1165_, lean_object* v_kind_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v_bi_boxed_1172_; uint8_t v_kind_boxed_1173_; lean_object* v_res_1174_; 
v_bi_boxed_1172_ = lean_unbox(v_bi_1163_);
v_kind_boxed_1173_ = lean_unbox(v_kind_1166_);
v_res_1174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(v_00_u03b1_1161_, v_name_1162_, v_bi_boxed_1172_, v_type_1164_, v_k_1165_, v_kind_boxed_1173_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_object* v_00_u03b1_1175_, lean_object* v_name_1176_, lean_object* v_type_1177_, lean_object* v_k_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_1176_, v_type_1177_, v_k_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_name_1186_, lean_object* v_type_1187_, lean_object* v_k_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(v_00_u03b1_1185_, v_name_1186_, v_type_1187_, v_k_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* v_00_u03b2_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1196_, v_x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_1199_, v_x_1200_, v_x_1201_);
lean_dec(v_x_1201_);
lean_dec_ref(v_x_1200_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1204_, lean_object* v_x_1205_, size_t v_x_1206_, lean_object* v_x_1207_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1205_, v_x_1206_, v_x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
size_t v_x_19947__boxed_1213_; uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_x_19947__boxed_1213_ = lean_unbox_usize(v_x_1211_);
lean_dec(v_x_1211_);
v_res_1214_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_1209_, v_x_1210_, v_x_19947__boxed_1213_, v_x_1212_);
lean_dec(v_x_1212_);
lean_dec_ref(v_x_1210_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_object* v_00_u03b2_1216_, lean_object* v_keys_1217_, lean_object* v_vals_1218_, lean_object* v_heq_1219_, lean_object* v_i_1220_, lean_object* v_k_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_1217_, v_i_1220_, v_k_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(lean_object* v_00_u03b2_1223_, lean_object* v_keys_1224_, lean_object* v_vals_1225_, lean_object* v_heq_1226_, lean_object* v_i_1227_, lean_object* v_k_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(v_00_u03b2_1223_, v_keys_1224_, v_vals_1225_, v_heq_1226_, v_i_1227_, v_k_1228_);
lean_dec(v_k_1228_);
lean_dec_ref(v_vals_1225_);
lean_dec_ref(v_keys_1224_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_BinderNameHint(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
