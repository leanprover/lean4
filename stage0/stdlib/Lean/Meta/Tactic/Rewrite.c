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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "motive is not type correct:"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__13 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__14;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nError: "};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__15 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__16;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 353, .m_capacity = 353, .m_length = 352, .m_data = "\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__17 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__17_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__18;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "' implies that 'm a = m b', which can be used with lemmas such as '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__19 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__20;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__21 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__21_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__22 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__22_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__23_value_aux_0),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__23 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__23_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 348, .m_capacity = 348, .m_length = 347, .m_data = "' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__24_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__26 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__26_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__27 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__27_value;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 118, .m_capacity = 118, .m_length = 117, .m_data = "' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well)."};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__28 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__28_value;
static lean_once_cell_t l_Lean_MVarId_rewrite___lam__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__29;
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_a"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__30 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__30_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(228, 106, 112, 29, 6, 211, 214, 169)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__31 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__31_value;
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
size_t v_x_18124__boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_x_18124__boxed_192_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_193_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_189_, v_x_18124__boxed_192_, v_x_191_);
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
lean_object* v___x_232_; lean_object* v___x_235_; 
v___x_232_ = lean_array_uget_borrowed(v_as_217_, v_i_218_);
v___x_235_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v___x_232_, v___y_222_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; uint8_t v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = lean_unbox(v_a_236_);
lean_dec(v_a_236_);
if (v___x_237_ == 0)
{
goto v___jp_233_;
}
else
{
v_a_227_ = v_b_220_;
goto v___jp_226_;
}
}
else
{
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_238_; uint8_t v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_235_, 1);
v___x_239_ = lean_unbox(v_a_238_);
lean_dec(v_a_238_);
if (v___x_239_ == 0)
{
v_a_227_ = v_b_220_;
goto v___jp_226_;
}
else
{
goto v___jp_233_;
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_b_220_);
v_a_240_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_235_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
v___jp_233_:
{
lean_object* v___x_234_; 
lean_inc(v___x_232_);
v___x_234_ = lean_array_push(v_b_220_, v___x_232_);
v_a_227_ = v___x_234_;
goto v___jp_226_;
}
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v_b_220_);
return v___x_248_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_stop_251_, lean_object* v_b_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
size_t v_i_boxed_258_; size_t v_stop_boxed_259_; lean_object* v_res_260_; 
v_i_boxed_258_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_stop_boxed_259_ = lean_unbox_usize(v_stop_251_);
lean_dec(v_stop_251_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_249_, v_i_boxed_258_, v_stop_boxed_259_, v_b_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec_ref(v_as_249_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object* v_k_261_, lean_object* v_b_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
lean_inc(v___y_266_);
lean_inc_ref(v___y_265_);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
v___x_268_ = lean_apply_6(v_k_261_, v_b_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, lean_box(0));
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_k_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_269_, v_b_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object* v_name_277_, uint8_t v_bi_278_, lean_object* v_type_279_, lean_object* v_k_280_, uint8_t v_kind_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_287_, 0, v_k_280_);
v___x_288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_277_, v_bi_278_, v_type_279_, v___f_287_, v_kind_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_288_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object* v_name_305_, lean_object* v_bi_306_, lean_object* v_type_307_, lean_object* v_k_308_, lean_object* v_kind_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v_bi_boxed_315_; uint8_t v_kind_boxed_316_; lean_object* v_res_317_; 
v_bi_boxed_315_ = lean_unbox(v_bi_306_);
v_kind_boxed_316_ = lean_unbox(v_kind_309_);
v_res_317_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_305_, v_bi_boxed_315_, v_type_307_, v_k_308_, v_kind_boxed_316_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object* v_name_318_, lean_object* v_type_319_, lean_object* v_k_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = 0;
v___x_327_ = 0;
v___x_328_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_318_, v___x_326_, v_type_319_, v_k_320_, v___x_327_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object* v_name_329_, lean_object* v_type_330_, lean_object* v_k_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_329_, v_type_330_, v_k_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_337_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(lean_object* v_a_338_, lean_object* v_as_339_, size_t v_i_340_, size_t v_stop_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_eq(v_i_340_, v_stop_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_array_uget_borrowed(v_as_339_, v_i_340_);
v___x_344_ = l_Lean_instBEqMVarId_beq(v_a_338_, v___x_343_);
if (v___x_344_ == 0)
{
size_t v___x_345_; size_t v___x_346_; 
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_add(v_i_340_, v___x_345_);
v_i_340_ = v___x_346_;
goto _start;
}
else
{
return v___x_344_;
}
}
else
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6___boxed(lean_object* v_a_349_, lean_object* v_as_350_, lean_object* v_i_351_, lean_object* v_stop_352_){
_start:
{
size_t v_i_boxed_353_; size_t v_stop_boxed_354_; uint8_t v_res_355_; lean_object* v_r_356_; 
v_i_boxed_353_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_stop_boxed_354_ = lean_unbox_usize(v_stop_352_);
lean_dec(v_stop_352_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_349_, v_as_350_, v_i_boxed_353_, v_stop_boxed_354_);
lean_dec_ref(v_as_350_);
lean_dec(v_a_349_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object* v_as_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v_as_357_);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
size_t v___x_362_; size_t v___x_363_; uint8_t v___x_364_; 
v___x_362_ = ((size_t)0ULL);
v___x_363_ = lean_usize_of_nat(v___x_360_);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_358_, v_as_357_, v___x_362_, v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* v_as_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_as_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object* v_a_369_, lean_object* v_as_370_, size_t v_i_371_, size_t v_stop_372_, lean_object* v_b_373_){
_start:
{
lean_object* v___y_375_; uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_eq(v_i_371_, v_stop_372_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_array_uget_borrowed(v_as_370_, v_i_371_);
v___x_381_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_a_369_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_inc(v___x_380_);
v___x_382_ = lean_array_push(v_b_373_, v___x_380_);
v___y_375_ = v___x_382_;
goto v___jp_374_;
}
else
{
v___y_375_ = v_b_373_;
goto v___jp_374_;
}
}
else
{
return v_b_373_;
}
v___jp_374_:
{
size_t v___x_376_; size_t v___x_377_; 
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_371_, v___x_376_);
v_i_371_ = v___x_377_;
v_b_373_ = v___y_375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* v_a_383_, lean_object* v_as_384_, lean_object* v_i_385_, lean_object* v_stop_386_, lean_object* v_b_387_){
_start:
{
size_t v_i_boxed_388_; size_t v_stop_boxed_389_; lean_object* v_res_390_; 
v_i_boxed_388_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_stop_boxed_389_ = lean_unbox_usize(v_stop_386_);
lean_dec(v_stop_386_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_383_, v_as_384_, v_i_boxed_388_, v_stop_boxed_389_, v_b_387_);
lean_dec_ref(v_as_384_);
lean_dec_ref(v_a_383_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(lean_object* v_msgData_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_env_398_; lean_object* v___x_399_; lean_object* v_toCold_400_; lean_object* v_mctx_401_; lean_object* v_lctx_402_; lean_object* v_options_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_397_ = lean_st_ref_get(v___y_395_);
v_env_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_env_398_);
lean_dec(v___x_397_);
v___x_399_ = lean_st_ref_get(v___y_393_);
v_toCold_400_ = lean_ctor_get(v___y_394_, 0);
v_mctx_401_ = lean_ctor_get(v___x_399_, 0);
lean_inc_ref(v_mctx_401_);
lean_dec(v___x_399_);
v_lctx_402_ = lean_ctor_get(v___y_392_, 2);
v_options_403_ = lean_ctor_get(v_toCold_400_, 2);
lean_inc_ref(v_options_403_);
lean_inc_ref(v_lctx_402_);
v___x_404_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_404_, 0, v_env_398_);
lean_ctor_set(v___x_404_, 1, v_mctx_401_);
lean_ctor_set(v___x_404_, 2, v_lctx_402_);
lean_ctor_set(v___x_404_, 3, v_options_403_);
v___x_405_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_msgData_391_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(lean_object* v_msgData_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_ref_420_; lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_ref_420_ = lean_ctor_get(v___y_417_, 2);
v___x_421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_ref_420_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_ref_420_);
lean_ctor_set(v___x_426_, 1, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__0));
v___x_440_ = l_Lean_stringToMessageData(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__2));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__7));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__9));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__11));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__13));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__15));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__17));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__19));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__24));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__28));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__32));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__34));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__36));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__38));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__46(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
v___x_508_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__45));
v___x_509_ = l_Lean_mkConst(v___x_508_, v___x_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* v_mvarId_510_, lean_object* v___x_511_, lean_object* v_heq_512_, lean_object* v_e_513_, lean_object* v_config_514_, uint8_t v_symm_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___x_549_; 
lean_inc(v___x_511_);
lean_inc(v_mvarId_510_);
v___x_549_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_510_, v___x_511_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
lean_dec_ref_known(v___x_549_, 1);
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc_ref(v_heq_512_);
v___x_550_ = lean_infer_type(v_heq_512_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_1086_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_a_551_, v___y_517_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_1086_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_1086_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = 0;
v___x_559_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_553_, v___x_557_, v___x_558_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v_snd_561_; lean_object* v_fst_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_1077_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v_snd_561_ = lean_ctor_get(v_a_560_, 1);
v_fst_562_ = lean_ctor_get(v_a_560_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_a_560_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_564_ = v_a_560_;
v_isShared_565_ = v_isSharedCheck_1077_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_561_);
lean_inc(v_fst_562_);
lean_dec(v_a_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_1077_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_1076_; 
v_fst_566_ = lean_ctor_get(v_snd_561_, 0);
v_snd_567_ = lean_ctor_get(v_snd_561_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_snd_561_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_569_ = v_snd_561_;
v_isShared_570_ = v_isSharedCheck_1076_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snd_567_);
lean_inc(v_fst_566_);
lean_dec(v_snd_561_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_1076_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___y_572_; lean_object* v___y_573_; size_t v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v_a_580_; lean_object* v___y_609_; lean_object* v___y_610_; size_t v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; uint8_t v___y_781_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v_eNew_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_972_; lean_object* v_heq_973_; lean_object* v_heqType_974_; lean_object* v_lhs_975_; lean_object* v_rhs_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v_heq_1000_; lean_object* v_heqType_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
lean_inc_ref(v_heq_512_);
v___x_1057_ = l_Lean_mkAppN(v_heq_512_, v_fst_562_);
v___x_1058_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__43));
v___x_1059_ = lean_unsigned_to_nat(2u);
v___x_1060_ = l_Lean_Expr_isAppOfArity(v_snd_567_, v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
v_heq_1000_ = v___x_1057_;
v_heqType_1001_ = v_snd_567_;
v___y_1002_ = v___y_516_;
v___y_1003_ = v___y_517_;
v___y_1004_ = v___y_518_;
v___y_1005_ = v___y_519_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = l_Lean_Expr_appFn_x21(v_snd_567_);
v___x_1062_ = l_Lean_Expr_appArg_x21(v___x_1061_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = l_Lean_Expr_appArg_x21(v_snd_567_);
lean_dec(v_snd_567_);
lean_inc_ref(v___x_1063_);
lean_inc_ref(v___x_1062_);
v___x_1064_ = l_Lean_Meta_mkEq(v___x_1062_, v___x_1063_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__46, &l_Lean_MVarId_rewrite___lam__1___closed__46_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__46);
v___x_1067_ = l_Lean_mkApp3(v___x_1066_, v___x_1062_, v___x_1063_, v___x_1057_);
v_heq_1000_ = v___x_1067_;
v_heqType_1001_ = v_a_1065_;
v___y_1002_ = v___y_516_;
v___y_1003_ = v___y_517_;
v___y_1004_ = v___y_518_;
v___y_1005_ = v___y_519_;
goto v___jp_999_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v___x_1063_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1057_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1068_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1064_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1064_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
v___jp_571_:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Meta_appendParentTag(v_mvarId_510_, v_fst_562_, v_fst_566_, v___y_579_, v___y_573_, v___y_577_, v___y_572_);
lean_dec(v_fst_566_);
lean_dec(v_fst_562_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_582_ = l_Lean_Meta_getMVarsNoDelayed(v_heq_512_, v___y_579_, v___y_573_, v___y_577_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_579_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = lean_array_get_size(v_a_583_);
v___x_585_ = lean_mk_empty_array_with_capacity(v___y_575_);
v___x_586_ = lean_nat_dec_lt(v___y_575_, v___x_584_);
if (v___x_586_ == 0)
{
lean_dec(v_a_583_);
v___y_541_ = v_a_580_;
v___y_542_ = v___y_576_;
v___y_543_ = v___y_578_;
v___y_544_ = v___x_585_;
goto v___jp_540_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = lean_nat_dec_le(v___x_584_, v___x_584_);
if (v___x_587_ == 0)
{
if (v___x_586_ == 0)
{
lean_dec(v_a_583_);
v___y_541_ = v_a_580_;
v___y_542_ = v___y_576_;
v___y_543_ = v___y_578_;
v___y_544_ = v___x_585_;
goto v___jp_540_;
}
else
{
size_t v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_usize_of_nat(v___x_584_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_580_, v_a_583_, v___y_574_, v___x_588_, v___x_585_);
lean_dec(v_a_583_);
v___y_541_ = v_a_580_;
v___y_542_ = v___y_576_;
v___y_543_ = v___y_578_;
v___y_544_ = v___x_589_;
goto v___jp_540_;
}
}
else
{
size_t v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_usize_of_nat(v___x_584_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_580_, v_a_583_, v___y_574_, v___x_590_, v___x_585_);
lean_dec(v_a_583_);
v___y_541_ = v_a_580_;
v___y_542_ = v___y_576_;
v___y_543_ = v___y_578_;
v___y_544_ = v___x_591_;
goto v___jp_540_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_a_580_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_576_);
v_a_592_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_582_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_582_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v_a_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v_heq_512_);
v_a_600_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_581_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_581_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
v___jp_608_:
{
if (lean_obj_tag(v___y_617_) == 0)
{
lean_object* v_a_618_; 
v_a_618_ = lean_ctor_get(v___y_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___y_617_, 1);
v___y_572_ = v___y_609_;
v___y_573_ = v___y_610_;
v___y_574_ = v___y_611_;
v___y_575_ = v___y_612_;
v___y_576_ = v___y_613_;
v___y_577_ = v___y_614_;
v___y_578_ = v___y_615_;
v___y_579_ = v___y_616_;
v_a_580_ = v_a_618_;
goto v___jp_571_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v_fst_566_);
lean_dec(v_fst_562_);
lean_dec_ref(v_heq_512_);
lean_dec(v_mvarId_510_);
v_a_619_ = lean_ctor_get(v___y_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___y_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___y_617_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___y_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
v___jp_627_:
{
uint8_t v___x_635_; lean_object* v___x_636_; 
v___x_635_ = 0;
lean_inc(v_fst_566_);
lean_inc(v_mvarId_510_);
v___x_636_ = l_Lean_Meta_postprocessAppMVars(v___x_511_, v_mvarId_510_, v_fst_562_, v_fst_566_, v___y_634_, v___x_635_, v___y_633_, v___y_629_, v___y_631_, v___y_628_);
if (lean_obj_tag(v___x_636_) == 0)
{
size_t v_sz_637_; size_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
lean_dec_ref_known(v___x_636_, 1);
v_sz_637_ = lean_array_size(v_fst_562_);
v___x_638_ = ((size_t)0ULL);
lean_inc(v_fst_562_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_637_, v___x_638_, v_fst_562_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_array_get_size(v___x_639_);
v___x_642_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__4));
v___x_643_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
if (v___x_643_ == 0)
{
lean_dec_ref(v___x_639_);
v___y_572_ = v___y_628_;
v___y_573_ = v___y_629_;
v___y_574_ = v___x_638_;
v___y_575_ = v___x_640_;
v___y_576_ = v___y_630_;
v___y_577_ = v___y_631_;
v___y_578_ = v___y_632_;
v___y_579_ = v___y_633_;
v_a_580_ = v___x_642_;
goto v___jp_571_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_le(v___x_641_, v___x_641_);
if (v___x_644_ == 0)
{
if (v___x_643_ == 0)
{
lean_dec_ref(v___x_639_);
v___y_572_ = v___y_628_;
v___y_573_ = v___y_629_;
v___y_574_ = v___x_638_;
v___y_575_ = v___x_640_;
v___y_576_ = v___y_630_;
v___y_577_ = v___y_631_;
v___y_578_ = v___y_632_;
v___y_579_ = v___y_633_;
v_a_580_ = v___x_642_;
goto v___jp_571_;
}
else
{
size_t v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_usize_of_nat(v___x_641_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_639_, v___x_638_, v___x_645_, v___x_642_, v___y_633_, v___y_629_, v___y_631_, v___y_628_);
lean_dec_ref(v___x_639_);
v___y_609_ = v___y_628_;
v___y_610_ = v___y_629_;
v___y_611_ = v___x_638_;
v___y_612_ = v___x_640_;
v___y_613_ = v___y_630_;
v___y_614_ = v___y_631_;
v___y_615_ = v___y_632_;
v___y_616_ = v___y_633_;
v___y_617_ = v___x_646_;
goto v___jp_608_;
}
}
else
{
size_t v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_usize_of_nat(v___x_641_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_639_, v___x_638_, v___x_647_, v___x_642_, v___y_633_, v___y_629_, v___y_631_, v___y_628_);
lean_dec_ref(v___x_639_);
v___y_609_ = v___y_628_;
v___y_610_ = v___y_629_;
v___y_611_ = v___x_638_;
v___y_612_ = v___x_640_;
v___y_613_ = v___y_630_;
v___y_614_ = v___y_631_;
v___y_615_ = v___y_632_;
v___y_616_ = v___y_633_;
v___y_617_ = v___x_648_;
goto v___jp_608_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
lean_dec(v_fst_566_);
lean_dec(v_fst_562_);
lean_dec_ref(v_heq_512_);
lean_dec(v_mvarId_510_);
v_a_649_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_636_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_636_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
v___jp_657_:
{
lean_object* v___x_669_; 
lean_inc_ref(v___y_658_);
v___x_669_ = l_Lean_Meta_getLevel(v___y_658_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
lean_inc_ref(v___y_661_);
v___x_671_ = l_Lean_Meta_getLevel(v___y_661_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_674_ = lean_box(0);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 1);
lean_ctor_set(v___x_569_, 1, v___x_674_);
lean_ctor_set(v___x_569_, 0, v_a_672_);
v___x_676_ = v___x_569_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_672_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_687_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 1);
lean_ctor_set(v___x_564_, 1, v___x_676_);
lean_ctor_set(v___x_564_, 0, v_a_670_);
v___x_678_ = v___x_564_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_686_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_679_ = l_Lean_Expr_const___override(v___x_673_, v___x_678_);
v___x_680_ = l_Lean_mkApp6(v___x_679_, v___y_658_, v___y_661_, v___y_664_, v___y_660_, v___y_659_, v___y_663_);
v___x_681_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_667_);
v___x_682_ = l_Lean_Meta_tactic_skipAssignedInstances;
v___x_683_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v___x_681_, v___x_682_);
lean_dec_ref(v___x_681_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; 
v___x_684_ = 1;
v___y_628_ = v___y_668_;
v___y_629_ = v___y_666_;
v___y_630_ = v___x_680_;
v___y_631_ = v___y_667_;
v___y_632_ = v___y_662_;
v___y_633_ = v___y_665_;
v___y_634_ = v___x_684_;
goto v___jp_627_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = 0;
v___y_628_ = v___y_668_;
v___y_629_ = v___y_666_;
v___y_630_ = v___x_680_;
v___y_631_ = v___y_667_;
v___y_632_ = v___y_662_;
v___y_633_ = v___y_665_;
v___y_634_ = v___x_685_;
goto v___jp_627_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_a_670_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec_ref(v___y_658_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_688_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_671_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_671_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec_ref(v___y_658_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_696_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_669_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_669_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
v___jp_704_:
{
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v___x_720_; 
lean_dec_ref_known(v___y_719_, 1);
lean_inc_ref(v___y_712_);
v___x_720_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v___y_713_, v___y_712_, v___y_718_, v___y_710_, v___y_711_, v___y_708_, v___y_715_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; uint8_t v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_unbox(v_a_721_);
lean_dec(v_a_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_723_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__8, &l_Lean_MVarId_rewrite___lam__1___closed__8_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__8);
lean_inc_ref(v___y_705_);
v___x_724_ = l_Lean_MessageData_ofExpr(v___y_705_);
v___x_725_ = l_Lean_indentD(v___x_724_);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_723_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__10, &l_Lean_MVarId_rewrite___lam__1___closed__10_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__10);
v___x_728_ = l_Lean_indentExpr(v___y_709_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__12, &l_Lean_MVarId_rewrite___lam__1___closed__12_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__12);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_inc_ref(v___y_717_);
v___x_732_ = l_Lean_indentExpr(v___y_717_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_MessageData_note(v___x_733_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_726_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 1);
lean_ctor_set(v___x_555_, 0, v___x_735_);
v___x_737_ = v___x_555_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_747_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
lean_inc(v_mvarId_510_);
lean_inc(v___x_511_);
v___x_738_ = l_Lean_Meta_throwTacticEx___redArg(v___x_511_, v_mvarId_510_, v___x_737_, v___y_710_, v___y_711_, v___y_708_, v___y_715_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_dec_ref_known(v___x_738_, 1);
v___y_658_ = v___y_712_;
v___y_659_ = v___y_705_;
v___y_660_ = v___y_706_;
v___y_661_ = v___y_714_;
v___y_662_ = v___y_716_;
v___y_663_ = v___y_707_;
v___y_664_ = v___y_717_;
v___y_665_ = v___y_710_;
v___y_666_ = v___y_711_;
v___y_667_ = v___y_708_;
v___y_668_ = v___y_715_;
goto v___jp_657_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
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
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_dec_ref(v___y_709_);
lean_del_object(v___x_555_);
v___y_658_ = v___y_712_;
v___y_659_ = v___y_705_;
v___y_660_ = v___y_706_;
v___y_661_ = v___y_714_;
v___y_662_ = v___y_716_;
v___y_663_ = v___y_707_;
v___y_664_ = v___y_717_;
v___y_665_ = v___y_710_;
v___y_666_ = v___y_711_;
v___y_667_ = v___y_708_;
v___y_668_ = v___y_715_;
goto v___jp_657_;
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_748_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_720_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_720_);
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
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_756_ = lean_ctor_get(v___y_719_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___y_719_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___y_719_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___y_719_);
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
v___jp_764_:
{
if (v___y_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v___y_767_);
v___x_782_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__14, &l_Lean_MVarId_rewrite___lam__1___closed__14_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__14);
lean_inc_ref(v___y_765_);
v___x_783_ = l_Lean_MessageData_ofExpr(v___y_765_);
v___x_784_ = l_Lean_indentD(v___x_783_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__16, &l_Lean_MVarId_rewrite___lam__1___closed__16_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__16);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_Exception_toMessageData(v___y_771_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__18, &l_Lean_MVarId_rewrite___lam__1___closed__18_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__18);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_793_ = l_Lean_MessageData_ofConstName(v___x_792_, v___y_781_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__20, &l_Lean_MVarId_rewrite___lam__1___closed__20_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__20);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__23));
v___x_798_ = l_Lean_MessageData_ofConstName(v___x_797_, v___y_781_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__25, &l_Lean_MVarId_rewrite___lam__1___closed__25_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__25);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__27));
v___x_803_ = l_Lean_MessageData_ofConstName(v___x_802_, v___y_781_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_801_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__29, &l_Lean_MVarId_rewrite___lam__1___closed__29_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__29);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_inc(v_mvarId_510_);
lean_inc(v___x_511_);
v___x_808_ = l_Lean_Meta_throwTacticEx___redArg(v___x_511_, v_mvarId_510_, v___x_807_, v___y_772_, v___y_773_, v___y_768_, v___y_777_);
v___y_705_ = v___y_765_;
v___y_706_ = v___y_766_;
v___y_707_ = v___y_769_;
v___y_708_ = v___y_768_;
v___y_709_ = v___y_770_;
v___y_710_ = v___y_772_;
v___y_711_ = v___y_773_;
v___y_712_ = v___y_774_;
v___y_713_ = v___y_775_;
v___y_714_ = v___y_776_;
v___y_715_ = v___y_777_;
v___y_716_ = v___y_778_;
v___y_717_ = v___y_779_;
v___y_718_ = v___y_780_;
v___y_719_ = v___x_808_;
goto v___jp_704_;
}
else
{
lean_dec_ref(v___y_771_);
v___y_705_ = v___y_765_;
v___y_706_ = v___y_766_;
v___y_707_ = v___y_769_;
v___y_708_ = v___y_768_;
v___y_709_ = v___y_770_;
v___y_710_ = v___y_772_;
v___y_711_ = v___y_773_;
v___y_712_ = v___y_774_;
v___y_713_ = v___y_775_;
v___y_714_ = v___y_776_;
v___y_715_ = v___y_777_;
v___y_716_ = v___y_778_;
v___y_717_ = v___y_779_;
v___y_718_ = v___y_780_;
v___y_719_ = v___y_767_;
goto v___jp_704_;
}
}
v___jp_809_:
{
lean_object* v___x_822_; 
lean_inc(v___y_821_);
lean_inc_ref(v___y_820_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc_ref(v___y_816_);
v___x_822_ = lean_infer_type(v___y_816_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___f_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_n(v_a_823_, 2);
lean_dec_ref_known(v___x_822_, 1);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(v___f_824_, 0, v___y_810_);
lean_closure_set(v___f_824_, 1, v_a_823_);
v___x_825_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__31));
v___x_826_ = 0;
lean_inc_ref(v___y_812_);
v___x_827_ = l_Lean_mkLambda(v___x_825_, v___x_826_, v___y_812_, v___y_811_);
v___x_828_ = 0;
lean_inc_ref(v___x_827_);
v___x_829_ = l_Lean_Meta_check(v___x_827_, v___x_828_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_829_) == 0)
{
v___y_705_ = v___x_827_;
v___y_706_ = v___y_813_;
v___y_707_ = v___y_814_;
v___y_708_ = v___y_820_;
v___y_709_ = v___y_816_;
v___y_710_ = v___y_818_;
v___y_711_ = v___y_819_;
v___y_712_ = v___y_812_;
v___y_713_ = v___x_825_;
v___y_714_ = v_a_823_;
v___y_715_ = v___y_821_;
v___y_716_ = v_eNew_817_;
v___y_717_ = v___y_815_;
v___y_718_ = v___f_824_;
v___y_719_ = v___x_829_;
goto v___jp_704_;
}
else
{
lean_object* v_a_830_; uint8_t v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
v___x_831_ = l_Lean_Exception_isInterrupt(v_a_830_);
if (v___x_831_ == 0)
{
uint8_t v___x_832_; 
lean_inc(v_a_830_);
v___x_832_ = l_Lean_Exception_isRuntime(v_a_830_);
v___y_765_ = v___x_827_;
v___y_766_ = v___y_813_;
v___y_767_ = v___x_829_;
v___y_768_ = v___y_820_;
v___y_769_ = v___y_814_;
v___y_770_ = v___y_816_;
v___y_771_ = v_a_830_;
v___y_772_ = v___y_818_;
v___y_773_ = v___y_819_;
v___y_774_ = v___y_812_;
v___y_775_ = v___x_825_;
v___y_776_ = v_a_823_;
v___y_777_ = v___y_821_;
v___y_778_ = v_eNew_817_;
v___y_779_ = v___y_815_;
v___y_780_ = v___f_824_;
v___y_781_ = v___x_832_;
goto v___jp_764_;
}
else
{
v___y_765_ = v___x_827_;
v___y_766_ = v___y_813_;
v___y_767_ = v___x_829_;
v___y_768_ = v___y_820_;
v___y_769_ = v___y_814_;
v___y_770_ = v___y_816_;
v___y_771_ = v_a_830_;
v___y_772_ = v___y_818_;
v___y_773_ = v___y_819_;
v___y_774_ = v___y_812_;
v___y_775_ = v___x_825_;
v___y_776_ = v_a_823_;
v___y_777_ = v___y_821_;
v___y_778_ = v_eNew_817_;
v___y_779_ = v___y_815_;
v___y_780_ = v___f_824_;
v___y_781_ = v___x_831_;
goto v___jp_764_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v_eNew_817_);
lean_dec_ref(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_833_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_822_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_822_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
v___jp_841_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_a_854_; uint8_t v___x_855_; 
v___x_852_ = lean_expr_instantiate1(v___y_842_, v___y_844_);
v___x_853_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v___x_852_, v___y_849_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref(v___x_853_);
v___x_855_ = l_Lean_Expr_hasBinderNameHint(v___y_844_);
if (v___x_855_ == 0)
{
lean_inc_ref(v___y_842_);
v___y_810_ = v___y_842_;
v___y_811_ = v___y_842_;
v___y_812_ = v___y_843_;
v___y_813_ = v___y_844_;
v___y_814_ = v___y_845_;
v___y_815_ = v___y_847_;
v___y_816_ = v___y_846_;
v_eNew_817_ = v_a_854_;
v___y_818_ = v___y_848_;
v___y_819_ = v___y_849_;
v___y_820_ = v___y_850_;
v___y_821_ = v___y_851_;
goto v___jp_809_;
}
else
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Expr_resolveBinderNameHint(v_a_854_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
lean_inc_ref(v___y_842_);
v___y_810_ = v___y_842_;
v___y_811_ = v___y_842_;
v___y_812_ = v___y_843_;
v___y_813_ = v___y_844_;
v___y_814_ = v___y_845_;
v___y_815_ = v___y_847_;
v___y_816_ = v___y_846_;
v_eNew_817_ = v_a_857_;
v___y_818_ = v___y_848_;
v___y_819_ = v___y_849_;
v___y_820_ = v___y_850_;
v___y_821_ = v___y_851_;
goto v___jp_809_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_842_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_858_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_856_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_856_);
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
v___jp_866_:
{
lean_object* v___x_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_970_; 
v___x_875_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_513_, v___y_872_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_970_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_970_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_970_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v_transparency_880_; uint8_t v_offsetCnstrs_881_; lean_object* v_occs_882_; lean_object* v___x_883_; uint8_t v_foApprox_884_; uint8_t v_ctxApprox_885_; uint8_t v_quasiPatternApprox_886_; uint8_t v_constApprox_887_; uint8_t v_isDefEqStuckEx_888_; uint8_t v_unificationHints_889_; uint8_t v_proofIrrelevance_890_; uint8_t v_assignSyntheticOpaque_891_; uint8_t v_etaStruct_892_; uint8_t v_univApprox_893_; uint8_t v_iota_894_; uint8_t v_beta_895_; uint8_t v_proj_896_; uint8_t v_zeta_897_; uint8_t v_zetaDelta_898_; uint8_t v_zetaUnused_899_; uint8_t v_zetaHave_900_; uint8_t v_canUnfoldPredicateConfig_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_969_; 
v_transparency_880_ = lean_ctor_get_uint8(v_config_514_, sizeof(void*)*1);
v_offsetCnstrs_881_ = lean_ctor_get_uint8(v_config_514_, sizeof(void*)*1 + 1);
v_occs_882_ = lean_ctor_get(v_config_514_, 0);
lean_inc(v_occs_882_);
lean_dec_ref(v_config_514_);
v___x_883_ = l_Lean_Meta_Context_config(v___y_871_);
v_foApprox_884_ = lean_ctor_get_uint8(v___x_883_, 0);
v_ctxApprox_885_ = lean_ctor_get_uint8(v___x_883_, 1);
v_quasiPatternApprox_886_ = lean_ctor_get_uint8(v___x_883_, 2);
v_constApprox_887_ = lean_ctor_get_uint8(v___x_883_, 3);
v_isDefEqStuckEx_888_ = lean_ctor_get_uint8(v___x_883_, 4);
v_unificationHints_889_ = lean_ctor_get_uint8(v___x_883_, 5);
v_proofIrrelevance_890_ = lean_ctor_get_uint8(v___x_883_, 6);
v_assignSyntheticOpaque_891_ = lean_ctor_get_uint8(v___x_883_, 7);
v_etaStruct_892_ = lean_ctor_get_uint8(v___x_883_, 10);
v_univApprox_893_ = lean_ctor_get_uint8(v___x_883_, 11);
v_iota_894_ = lean_ctor_get_uint8(v___x_883_, 12);
v_beta_895_ = lean_ctor_get_uint8(v___x_883_, 13);
v_proj_896_ = lean_ctor_get_uint8(v___x_883_, 14);
v_zeta_897_ = lean_ctor_get_uint8(v___x_883_, 15);
v_zetaDelta_898_ = lean_ctor_get_uint8(v___x_883_, 16);
v_zetaUnused_899_ = lean_ctor_get_uint8(v___x_883_, 17);
v_zetaHave_900_ = lean_ctor_get_uint8(v___x_883_, 18);
v_canUnfoldPredicateConfig_901_ = lean_ctor_get_uint8(v___x_883_, 19);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_969_ == 0)
{
v___x_903_ = v___x_883_;
v_isShared_904_ = v_isSharedCheck_969_;
goto v_resetjp_902_;
}
else
{
lean_dec(v___x_883_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_969_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v_trackZetaDelta_905_; lean_object* v_zetaDeltaSet_906_; lean_object* v_lctx_907_; lean_object* v_localInstances_908_; lean_object* v_defEqCtx_x3f_909_; lean_object* v_synthPendingDepth_910_; lean_object* v_customCanUnfoldPredicate_x3f_911_; uint8_t v_univApprox_912_; uint8_t v_inTypeClassResolution_913_; uint8_t v_cacheInferType_914_; lean_object* v___x_916_; 
v_trackZetaDelta_905_ = lean_ctor_get_uint8(v___y_871_, sizeof(void*)*7);
v_zetaDeltaSet_906_ = lean_ctor_get(v___y_871_, 1);
v_lctx_907_ = lean_ctor_get(v___y_871_, 2);
v_localInstances_908_ = lean_ctor_get(v___y_871_, 3);
v_defEqCtx_x3f_909_ = lean_ctor_get(v___y_871_, 4);
v_synthPendingDepth_910_ = lean_ctor_get(v___y_871_, 5);
v_customCanUnfoldPredicate_x3f_911_ = lean_ctor_get(v___y_871_, 6);
v_univApprox_912_ = lean_ctor_get_uint8(v___y_871_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_913_ = lean_ctor_get_uint8(v___y_871_, sizeof(void*)*7 + 2);
v_cacheInferType_914_ = lean_ctor_get_uint8(v___y_871_, sizeof(void*)*7 + 3);
if (v_isShared_904_ == 0)
{
v___x_916_ = v___x_903_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 0, v_foApprox_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 1, v_ctxApprox_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 2, v_quasiPatternApprox_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 3, v_constApprox_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 4, v_isDefEqStuckEx_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 5, v_unificationHints_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 6, v_proofIrrelevance_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 7, v_assignSyntheticOpaque_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 10, v_etaStruct_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 11, v_univApprox_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 12, v_iota_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 13, v_beta_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 14, v_proj_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 15, v_zeta_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 16, v_zetaDelta_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 17, v_zetaUnused_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 18, v_zetaHave_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, 19, v_canUnfoldPredicateConfig_901_);
v___x_916_ = v_reuseFailAlloc_968_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
uint64_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_ctor_set_uint8(v___x_916_, 8, v_offsetCnstrs_881_);
lean_ctor_set_uint8(v___x_916_, 9, v_transparency_880_);
v___x_917_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set_uint64(v___x_918_, sizeof(void*)*1, v___x_917_);
lean_inc(v_customCanUnfoldPredicate_x3f_911_);
lean_inc(v_synthPendingDepth_910_);
lean_inc(v_defEqCtx_x3f_909_);
lean_inc_ref(v_localInstances_908_);
lean_inc_ref(v_lctx_907_);
lean_inc(v_zetaDeltaSet_906_);
v___x_919_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v_zetaDeltaSet_906_);
lean_ctor_set(v___x_919_, 2, v_lctx_907_);
lean_ctor_set(v___x_919_, 3, v_localInstances_908_);
lean_ctor_set(v___x_919_, 4, v_defEqCtx_x3f_909_);
lean_ctor_set(v___x_919_, 5, v_synthPendingDepth_910_);
lean_ctor_set(v___x_919_, 6, v_customCanUnfoldPredicate_x3f_911_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*7, v_trackZetaDelta_905_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*7 + 1, v_univApprox_912_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*7 + 2, v_inTypeClassResolution_913_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*7 + 3, v_cacheInferType_914_);
lean_inc_ref(v___y_870_);
lean_inc(v_a_876_);
v___x_920_ = l_Lean_Meta_kabstract(v_a_876_, v___y_870_, v_occs_882_, v___x_919_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; uint8_t v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = l_Lean_Expr_hasLooseBVars(v_a_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_inc_ref(v___y_870_);
lean_inc(v_a_876_);
v___x_923_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_876_, v___y_870_, v___x_919_, v___y_872_, v___y_873_, v___y_874_);
lean_dec_ref_known(v___x_919_, 7);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v_fst_925_; lean_object* v_snd_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_951_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v_fst_925_ = lean_ctor_get(v_a_924_, 0);
v_snd_926_ = lean_ctor_get(v_a_924_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_951_ == 0)
{
v___x_928_ = v_a_924_;
v_isShared_929_ = v_isSharedCheck_951_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snd_926_);
lean_inc(v_fst_925_);
lean_dec(v_a_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_951_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__33, &l_Lean_MVarId_rewrite___lam__1___closed__33_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__33);
v___x_931_ = l_Lean_indentExpr(v_snd_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 7);
lean_ctor_set(v___x_928_, 1, v___x_931_);
lean_ctor_set(v___x_928_, 0, v___x_930_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_950_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_934_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__35, &l_Lean_MVarId_rewrite___lam__1___closed__35_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__35);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_indentExpr(v_fst_925_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 1);
lean_ctor_set(v___x_878_, 0, v___x_937_);
v___x_939_ = v___x_878_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_949_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
lean_inc(v_mvarId_510_);
lean_inc(v___x_511_);
v___x_940_ = l_Lean_Meta_throwTacticEx___redArg(v___x_511_, v_mvarId_510_, v___x_939_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_dec_ref_known(v___x_940_, 1);
v___y_842_ = v_a_921_;
v___y_843_ = v___y_867_;
v___y_844_ = v___y_868_;
v___y_845_ = v___y_869_;
v___y_846_ = v_a_876_;
v___y_847_ = v___y_870_;
v___y_848_ = v___y_871_;
v___y_849_ = v___y_872_;
v___y_850_ = v___y_873_;
v___y_851_ = v___y_874_;
goto v___jp_841_;
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_921_);
lean_dec(v_a_876_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v___y_867_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_a_921_);
lean_del_object(v___x_878_);
lean_dec(v_a_876_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v___y_867_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_952_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_923_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_923_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_919_, 7);
lean_del_object(v___x_878_);
v___y_842_ = v_a_921_;
v___y_843_ = v___y_867_;
v___y_844_ = v___y_868_;
v___y_845_ = v___y_869_;
v___y_846_ = v_a_876_;
v___y_847_ = v___y_870_;
v___y_848_ = v___y_871_;
v___y_849_ = v___y_872_;
v___y_850_ = v___y_873_;
v___y_851_ = v___y_874_;
goto v___jp_841_;
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref_known(v___x_919_, 7);
lean_del_object(v___x_878_);
lean_dec(v_a_876_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v___y_867_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_960_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_920_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_920_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
}
v___jp_971_:
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_Expr_getAppFn(v_lhs_975_);
v___x_982_ = l_Lean_Expr_isMVar(v___x_981_);
lean_dec_ref(v___x_981_);
if (v___x_982_ == 0)
{
lean_dec_ref(v_heqType_974_);
v___y_867_ = v___y_972_;
v___y_868_ = v_rhs_976_;
v___y_869_ = v_heq_973_;
v___y_870_ = v_lhs_975_;
v___y_871_ = v___y_977_;
v___y_872_ = v___y_978_;
v___y_873_ = v___y_979_;
v___y_874_ = v___y_980_;
goto v___jp_866_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_rhs_976_);
lean_dec_ref(v_heq_973_);
lean_dec_ref(v___y_972_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v___x_983_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__37, &l_Lean_MVarId_rewrite___lam__1___closed__37_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__37);
v___x_984_ = l_Lean_MessageData_ofExpr(v_lhs_975_);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__39, &l_Lean_MVarId_rewrite___lam__1___closed__39_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__39);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_indentExpr(v_heqType_974_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_989_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
v___jp_999_:
{
lean_object* v___x_1006_; 
lean_inc_ref(v_heqType_1001_);
v___x_1006_ = l_Lean_Meta_matchEq_x3f(v_heqType_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_object* v___x_1008_; 
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
lean_inc_ref(v_heqType_1001_);
v___x_1008_ = l_Lean_Meta_isProp(v_heqType_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; uint8_t v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_unbox(v_a_1009_);
lean_dec(v_a_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__40));
v___y_522_ = v___y_1003_;
v___y_523_ = v_heq_1000_;
v___y_524_ = v___y_1002_;
v___y_525_ = v___y_1004_;
v___y_526_ = v_heqType_1001_;
v___y_527_ = v___y_1005_;
v___y_528_ = v___x_1011_;
goto v___jp_521_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__41));
v___y_522_ = v___y_1003_;
v___y_523_ = v_heq_1000_;
v___y_524_ = v___y_1002_;
v___y_525_ = v___y_1004_;
v___y_526_ = v_heqType_1001_;
v___y_527_ = v___y_1005_;
v___y_528_ = v___x_1012_;
goto v___jp_521_;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_heqType_1001_);
lean_dec_ref(v_heq_1000_);
v_a_1013_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1008_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1008_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_val_1021_; lean_object* v_snd_1022_; 
v_val_1021_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v_a_1007_, 1);
v_snd_1022_ = lean_ctor_get(v_val_1021_, 1);
lean_inc(v_snd_1022_);
if (v_symm_515_ == 0)
{
lean_object* v_fst_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; 
v_fst_1023_ = lean_ctor_get(v_val_1021_, 0);
lean_inc(v_fst_1023_);
lean_dec(v_val_1021_);
v_fst_1024_ = lean_ctor_get(v_snd_1022_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v_snd_1022_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_snd_1022_);
v___y_972_ = v_fst_1023_;
v_heq_973_ = v_heq_1000_;
v_heqType_974_ = v_heqType_1001_;
v_lhs_975_ = v_fst_1024_;
v_rhs_976_ = v_snd_1025_;
v___y_977_ = v___y_1002_;
v___y_978_ = v___y_1003_;
v___y_979_ = v___y_1004_;
v___y_980_ = v___y_1005_;
goto v___jp_971_;
}
else
{
lean_object* v_fst_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_heqType_1001_);
v_fst_1026_ = lean_ctor_get(v_val_1021_, 0);
lean_inc(v_fst_1026_);
lean_dec(v_val_1021_);
v_fst_1027_ = lean_ctor_get(v_snd_1022_, 0);
lean_inc(v_fst_1027_);
v_snd_1028_ = lean_ctor_get(v_snd_1022_, 1);
lean_inc(v_snd_1028_);
lean_dec(v_snd_1022_);
v___x_1029_ = l_Lean_Meta_mkEqSymm(v_heq_1000_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
lean_inc(v_fst_1027_);
lean_inc(v_snd_1028_);
v___x_1031_ = l_Lean_Meta_mkEq(v_snd_1028_, v_fst_1027_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___y_972_ = v_fst_1026_;
v_heq_973_ = v_a_1030_;
v_heqType_974_ = v_a_1032_;
v_lhs_975_ = v_snd_1028_;
v_rhs_976_ = v_fst_1027_;
v___y_977_ = v___y_1002_;
v___y_978_ = v___y_1003_;
v___y_979_ = v___y_1004_;
v___y_980_ = v___y_1005_;
goto v___jp_971_;
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_a_1030_);
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec(v_fst_1026_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1033_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1031_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec(v_fst_1026_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1041_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1029_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1029_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_heqType_1001_);
lean_dec_ref(v_heq_1000_);
lean_del_object(v___x_569_);
lean_dec(v_fst_566_);
lean_del_object(v___x_564_);
lean_dec(v_fst_562_);
lean_del_object(v___x_555_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1049_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1006_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1006_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_555_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1078_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_559_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_559_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1087_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_550_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_550_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_config_514_);
lean_dec_ref(v_e_513_);
lean_dec_ref(v_heq_512_);
lean_dec(v___x_511_);
lean_dec(v_mvarId_510_);
v_a_1095_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_549_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_549_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
v___jp_521_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_529_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__1, &l_Lean_MVarId_rewrite___lam__1___closed__1_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__1);
v___x_530_ = lean_unsigned_to_nat(30u);
v___x_531_ = l_Lean_inlineExpr(v___y_523_, v___x_530_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__3, &l_Lean_MVarId_rewrite___lam__1___closed__3_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__3);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc_ref(v___y_528_);
v___x_535_ = l_Lean_stringToMessageData(v___y_528_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_indentExpr(v___y_526_);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_538_, v___y_524_, v___y_522_, v___y_525_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_524_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_545_ = l_Array_append___redArg(v___y_541_, v___y_544_);
lean_dec_ref(v___y_544_);
v___x_546_ = lean_array_to_list(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_547_, 0, v___y_543_);
lean_ctor_set(v___x_547_, 1, v___y_542_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* v_mvarId_1103_, lean_object* v___x_1104_, lean_object* v_heq_1105_, lean_object* v_e_1106_, lean_object* v_config_1107_, lean_object* v_symm_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_symm_boxed_1114_; lean_object* v_res_1115_; 
v_symm_boxed_1114_ = lean_unbox(v_symm_1108_);
v_res_1115_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_1103_, v___x_1104_, v_heq_1105_, v_e_1106_, v_config_1107_, v_symm_boxed_1114_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* v_mvarId_1119_, lean_object* v_e_1120_, lean_object* v_heq_1121_, uint8_t v_symm_1122_, lean_object* v_config_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v___x_1129_ = ((lean_object*)(l_Lean_MVarId_rewrite___closed__1));
v___x_1130_ = lean_box(v_symm_1122_);
lean_inc(v_mvarId_1119_);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1131_, 0, v_mvarId_1119_);
lean_closure_set(v___f_1131_, 1, v___x_1129_);
lean_closure_set(v___f_1131_, 2, v_heq_1121_);
lean_closure_set(v___f_1131_, 3, v_e_1120_);
lean_closure_set(v___f_1131_, 4, v_config_1123_);
lean_closure_set(v___f_1131_, 5, v___x_1130_);
v___x_1132_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_1119_, v___f_1131_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* v_mvarId_1133_, lean_object* v_e_1134_, lean_object* v_heq_1135_, lean_object* v_symm_1136_, lean_object* v_config_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
uint8_t v_symm_boxed_1143_; lean_object* v_res_1144_; 
v_symm_boxed_1143_ = lean_unbox(v_symm_1136_);
v_res_1144_ = l_Lean_MVarId_rewrite(v_mvarId_1133_, v_e_1134_, v_heq_1135_, v_symm_boxed_1143_, v_config_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* v_mvarId_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_1145_, v___y_1147_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* v_mvarId_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v_mvarId_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object* v_00_u03b1_1159_, lean_object* v_msg_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_msg_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(v_00_u03b1_1167_, v_msg_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_object* v_00_u03b1_1175_, lean_object* v_name_1176_, uint8_t v_bi_1177_, lean_object* v_type_1178_, lean_object* v_k_1179_, uint8_t v_kind_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1176_, v_bi_1177_, v_type_1178_, v_k_1179_, v_kind_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_name_1188_, lean_object* v_bi_1189_, lean_object* v_type_1190_, lean_object* v_k_1191_, lean_object* v_kind_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_bi_boxed_1198_; uint8_t v_kind_boxed_1199_; lean_object* v_res_1200_; 
v_bi_boxed_1198_ = lean_unbox(v_bi_1189_);
v_kind_boxed_1199_ = lean_unbox(v_kind_1192_);
v_res_1200_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(v_00_u03b1_1187_, v_name_1188_, v_bi_boxed_1198_, v_type_1190_, v_k_1191_, v_kind_boxed_1199_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_object* v_00_u03b1_1201_, lean_object* v_name_1202_, lean_object* v_type_1203_, lean_object* v_k_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_1202_, v_type_1203_, v_k_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_name_1212_, lean_object* v_type_1213_, lean_object* v_k_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(v_00_u03b1_1211_, v_name_1212_, v_type_1213_, v_k_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* v_00_u03b2_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1222_, v_x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_1225_, v_x_1226_, v_x_1227_);
lean_dec(v_x_1227_);
lean_dec_ref(v_x_1226_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1230_, lean_object* v_x_1231_, size_t v_x_1232_, lean_object* v_x_1233_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1231_, v_x_1232_, v_x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
size_t v_x_19881__boxed_1239_; uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_x_19881__boxed_1239_ = lean_unbox_usize(v_x_1237_);
lean_dec(v_x_1237_);
v_res_1240_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_1235_, v_x_1236_, v_x_19881__boxed_1239_, v_x_1238_);
lean_dec(v_x_1238_);
lean_dec_ref(v_x_1236_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_object* v_00_u03b2_1242_, lean_object* v_keys_1243_, lean_object* v_vals_1244_, lean_object* v_heq_1245_, lean_object* v_i_1246_, lean_object* v_k_1247_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_1243_, v_i_1246_, v_k_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(lean_object* v_00_u03b2_1249_, lean_object* v_keys_1250_, lean_object* v_vals_1251_, lean_object* v_heq_1252_, lean_object* v_i_1253_, lean_object* v_k_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(v_00_u03b2_1249_, v_keys_1250_, v_vals_1251_, v_heq_1252_, v_i_1253_, v_k_1254_);
lean_dec(v_k_1254_);
lean_dec_ref(v_vals_1251_);
lean_dec_ref(v_keys_1250_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
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
