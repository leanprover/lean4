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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_MVarId_rewrite___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__4 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_MVarId_rewrite___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_MVarId_rewrite___lam__1___closed__5 = (const lean_object*)&l_Lean_MVarId_rewrite___lam__1___closed__5_value;
static const lean_array_object l_Lean_MVarId_rewrite___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__3(lean_object* v_opts_45_, lean_object* v_opt_46_){
_start:
{
lean_object* v_name_47_; lean_object* v_defValue_48_; lean_object* v_map_49_; lean_object* v___x_50_; 
v_name_47_ = lean_ctor_get(v_opt_46_, 0);
v_defValue_48_ = lean_ctor_get(v_opt_46_, 1);
v_map_49_ = lean_ctor_get(v_opts_45_, 0);
v___x_50_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_49_, v_name_47_);
if (lean_obj_tag(v___x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = lean_unbox(v_defValue_48_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; 
v_val_52_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_val_52_);
lean_dec_ref_known(v___x_50_, 1);
if (lean_obj_tag(v_val_52_) == 1)
{
uint8_t v_v_53_; 
v_v_53_ = lean_ctor_get_uint8(v_val_52_, 0);
lean_dec_ref_known(v_val_52_, 0);
return v_v_53_;
}
else
{
uint8_t v___x_54_; 
lean_dec(v_val_52_);
v___x_54_ = lean_unbox(v_defValue_48_);
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object* v_opts_55_, lean_object* v_opt_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__3(v_opts_55_, v_opt_56_);
lean_dec_ref(v_opt_56_);
lean_dec_ref(v_opts_55_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(lean_object* v_mvarId_59_, lean_object* v_x_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_66_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_66_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg___boxed(lean_object* v_mvarId_83_, lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_83_, v_x_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(lean_object* v_00_u03b1_91_, lean_object* v_mvarId_92_, lean_object* v_x_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_92_, v_x_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___boxed(lean_object* v_00_u03b1_100_, lean_object* v_mvarId_101_, lean_object* v_x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(v_00_u03b1_100_, v_mvarId_101_, v_x_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_expr_instantiate1(v_a_109_, v_a_111_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
v___x_118_ = lean_infer_type(v___x_117_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_Meta_isExprDefEq(v_a_119_, v_a_110_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v_a_110_);
v_a_121_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_118_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_118_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_MVarId_rewrite___lam__0(v_a_129_, v_a_130_, v_a_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec_ref(v_a_131_);
lean_dec_ref(v_a_129_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__5_spec__7(lean_object* v_a_138_, lean_object* v_as_139_, size_t v_i_140_, size_t v_stop_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_eq(v_i_140_, v_stop_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_array_uget_borrowed(v_as_139_, v_i_140_);
v___x_144_ = l_Lean_instBEqMVarId_beq(v_a_138_, v___x_143_);
if (v___x_144_ == 0)
{
size_t v___x_145_; size_t v___x_146_; 
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_i_140_, v___x_145_);
v_i_140_ = v___x_146_;
goto _start;
}
else
{
return v___x_144_;
}
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__5_spec__7___boxed(lean_object* v_a_149_, lean_object* v_as_150_, lean_object* v_i_151_, lean_object* v_stop_152_){
_start:
{
size_t v_i_boxed_153_; size_t v_stop_boxed_154_; uint8_t v_res_155_; lean_object* v_r_156_; 
v_i_boxed_153_ = lean_unbox_usize(v_i_151_);
lean_dec(v_i_151_);
v_stop_boxed_154_ = lean_unbox_usize(v_stop_152_);
lean_dec(v_stop_152_);
v_res_155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__5_spec__7(v_a_149_, v_as_150_, v_i_boxed_153_, v_stop_boxed_154_);
lean_dec_ref(v_as_150_);
lean_dec(v_a_149_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__5(lean_object* v_as_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_array_get_size(v_as_157_);
v___x_161_ = lean_nat_dec_lt(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
return v___x_161_;
}
else
{
if (v___x_161_ == 0)
{
return v___x_161_;
}
else
{
size_t v___x_162_; size_t v___x_163_; uint8_t v___x_164_; 
v___x_162_ = ((size_t)0ULL);
v___x_163_ = lean_usize_of_nat(v___x_160_);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__5_spec__7(v_a_158_, v_as_157_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* v_as_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__5(v_as_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_as_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object* v_a_169_, lean_object* v_as_170_, size_t v_i_171_, size_t v_stop_172_, lean_object* v_b_173_){
_start:
{
lean_object* v___y_175_; uint8_t v___x_179_; 
v___x_179_ = lean_usize_dec_eq(v_i_171_, v_stop_172_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; uint8_t v___x_182_; 
v___x_180_ = lean_array_uget_borrowed(v_as_170_, v_i_171_);
v___x_181_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__5(v_a_169_, v___x_180_);
v___x_182_ = lean_bool_not(v___x_181_);
if (v___x_182_ == 0)
{
v___y_175_ = v_b_173_;
goto v___jp_174_;
}
else
{
lean_object* v___x_183_; 
lean_inc(v___x_180_);
v___x_183_ = lean_array_push(v_b_173_, v___x_180_);
v___y_175_ = v___x_183_;
goto v___jp_174_;
}
}
else
{
return v_b_173_;
}
v___jp_174_:
{
size_t v___x_176_; size_t v___x_177_; 
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_add(v_i_171_, v___x_176_);
v_i_171_ = v___x_177_;
v_b_173_ = v___y_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object* v_a_184_, lean_object* v_as_185_, lean_object* v_i_186_, lean_object* v_stop_187_, lean_object* v_b_188_){
_start:
{
size_t v_i_boxed_189_; size_t v_stop_boxed_190_; lean_object* v_res_191_; 
v_i_boxed_189_ = lean_unbox_usize(v_i_186_);
lean_dec(v_i_186_);
v_stop_boxed_190_ = lean_unbox_usize(v_stop_187_);
lean_dec(v_stop_187_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_a_184_, v_as_185_, v_i_boxed_189_, v_stop_boxed_190_, v_b_188_);
lean_dec_ref(v_as_185_);
lean_dec_ref(v_a_184_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__4(size_t v_sz_192_, size_t v_i_193_, lean_object* v_bs_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_usize_dec_lt(v_i_193_, v_sz_192_);
if (v___x_195_ == 0)
{
return v_bs_194_;
}
else
{
lean_object* v_v_196_; lean_object* v___x_197_; lean_object* v_bs_x27_198_; lean_object* v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; 
v_v_196_ = lean_array_uget(v_bs_194_, v_i_193_);
v___x_197_ = lean_unsigned_to_nat(0u);
v_bs_x27_198_ = lean_array_uset(v_bs_194_, v_i_193_, v___x_197_);
v___x_199_ = l_Lean_Expr_mvarId_x21(v_v_196_);
lean_dec(v_v_196_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_add(v_i_193_, v___x_200_);
v___x_202_ = lean_array_uset(v_bs_x27_198_, v_i_193_, v___x_199_);
v_i_193_ = v___x_201_;
v_bs_194_ = v___x_202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* v_sz_204_, lean_object* v_i_205_, lean_object* v_bs_206_){
_start:
{
size_t v_sz_boxed_207_; size_t v_i_boxed_208_; lean_object* v_res_209_; 
v_sz_boxed_207_ = lean_unbox_usize(v_sz_204_);
lean_dec(v_sz_204_);
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__4(v_sz_boxed_207_, v_i_boxed_208_, v_bs_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object* v_k_210_, lean_object* v_b_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; 
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
v___x_217_ = lean_apply_6(v_k_210_, v_b_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, lean_box(0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_k_218_, lean_object* v_b_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_218_, v_b_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object* v_name_226_, uint8_t v_bi_227_, lean_object* v_type_228_, lean_object* v_k_229_, uint8_t v_kind_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___f_236_; lean_object* v___x_237_; 
v___f_236_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_236_, 0, v_k_229_);
v___x_237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_226_, v_bi_227_, v_type_228_, v___f_236_, v_kind_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_a_246_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_237_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_237_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object* v_name_254_, lean_object* v_bi_255_, lean_object* v_type_256_, lean_object* v_k_257_, lean_object* v_kind_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v_bi_boxed_264_; uint8_t v_kind_boxed_265_; lean_object* v_res_266_; 
v_bi_boxed_264_ = lean_unbox(v_bi_255_);
v_kind_boxed_265_ = lean_unbox(v_kind_258_);
v_res_266_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_254_, v_bi_boxed_264_, v_type_256_, v_k_257_, v_kind_boxed_265_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object* v_name_267_, lean_object* v_type_268_, lean_object* v_k_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
uint8_t v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = 0;
v___x_276_ = 0;
v___x_277_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_267_, v___x_275_, v_type_268_, v_k_269_, v___x_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object* v_name_278_, lean_object* v_type_279_, lean_object* v_k_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_278_, v_type_279_, v_k_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(lean_object* v_keys_287_, lean_object* v_i_288_, lean_object* v_k_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_keys_287_);
v___x_291_ = lean_nat_dec_lt(v_i_288_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_i_288_);
return v___x_291_;
}
else
{
lean_object* v_k_x27_292_; uint8_t v___x_293_; 
v_k_x27_292_ = lean_array_fget_borrowed(v_keys_287_, v_i_288_);
v___x_293_ = l_Lean_instBEqMVarId_beq(v_k_289_, v_k_x27_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_i_288_, v___x_294_);
lean_dec(v_i_288_);
v_i_288_ = v___x_295_;
goto _start;
}
else
{
lean_dec(v_i_288_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg___boxed(lean_object* v_keys_297_, lean_object* v_i_298_, lean_object* v_k_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_297_, v_i_298_, v_k_299_);
lean_dec(v_k_299_);
lean_dec_ref(v_keys_297_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object* v_x_302_, size_t v_x_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v_es_305_; lean_object* v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v_j_309_; lean_object* v___x_310_; 
v_es_305_ = lean_ctor_get(v_x_302_, 0);
v___x_306_ = lean_box(2);
v___x_307_ = ((size_t)31ULL);
v___x_308_ = lean_usize_land(v_x_303_, v___x_307_);
v_j_309_ = lean_usize_to_nat(v___x_308_);
v___x_310_ = lean_array_get_borrowed(v___x_306_, v_es_305_, v_j_309_);
lean_dec(v_j_309_);
switch(lean_obj_tag(v___x_310_))
{
case 0:
{
lean_object* v_key_311_; uint8_t v___x_312_; 
v_key_311_ = lean_ctor_get(v___x_310_, 0);
v___x_312_ = l_Lean_instBEqMVarId_beq(v_x_304_, v_key_311_);
return v___x_312_;
}
case 1:
{
lean_object* v_node_313_; size_t v___x_314_; size_t v___x_315_; 
v_node_313_ = lean_ctor_get(v___x_310_, 0);
v___x_314_ = ((size_t)5ULL);
v___x_315_ = lean_usize_shift_right(v_x_303_, v___x_314_);
v_x_302_ = v_node_313_;
v_x_303_ = v___x_315_;
goto _start;
}
default: 
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
}
}
else
{
lean_object* v_ks_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_ks_318_ = lean_ctor_get(v_x_302_, 0);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_ks_318_, v___x_319_, v_x_304_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
size_t v_x_18161__boxed_324_; uint8_t v_res_325_; lean_object* v_r_326_; 
v_x_18161__boxed_324_ = lean_unbox_usize(v_x_322_);
lean_dec(v_x_322_);
v_res_325_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_321_, v_x_18161__boxed_324_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_x_321_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
uint64_t v___x_329_; size_t v___x_330_; uint8_t v___x_331_; 
v___x_329_ = l_Lean_instHashableMVarId_hash(v_x_328_);
v___x_330_ = lean_uint64_to_usize(v___x_329_);
v___x_331_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_327_, v___x_330_, v_x_328_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_x_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object* v_mvarId_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; lean_object* v_mctx_340_; lean_object* v_eAssignment_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_339_ = lean_st_ref_get(v___y_337_);
v_mctx_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc_ref(v_mctx_340_);
lean_dec(v___x_339_);
v_eAssignment_341_ = lean_ctor_get(v_mctx_340_, 8);
lean_inc_ref(v_eAssignment_341_);
lean_dec_ref(v_mctx_340_);
v___x_342_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_eAssignment_341_, v_mvarId_336_);
lean_dec_ref(v_eAssignment_341_);
v___x_343_ = lean_box(v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* v_mvarId_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec(v_mvarId_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7(lean_object* v_as_349_, size_t v_i_350_, size_t v_stop_351_, lean_object* v_b_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_a_359_; uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_eq(v_i_350_, v_stop_351_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v_a_366_; lean_object* v___x_368_; 
v___x_364_ = lean_array_uget_borrowed(v_as_349_, v_i_350_);
v___x_368_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v___x_364_, v___y_354_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; uint8_t v___x_370_; uint8_t v___x_371_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = lean_unbox(v_a_369_);
lean_dec(v_a_369_);
v___x_371_ = lean_bool_not(v___x_370_);
v_a_366_ = v___x_371_;
goto v___jp_365_;
}
else
{
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_372_; uint8_t v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_368_, 1);
v___x_373_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
v_a_366_ = v___x_373_;
goto v___jp_365_;
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_b_352_);
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
v___jp_365_:
{
if (v_a_366_ == 0)
{
v_a_359_ = v_b_352_;
goto v___jp_358_;
}
else
{
lean_object* v___x_367_; 
lean_inc(v___x_364_);
v___x_367_ = lean_array_push(v_b_352_, v___x_364_);
v_a_359_ = v___x_367_;
goto v___jp_358_;
}
}
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_b_352_);
return v___x_382_;
}
v___jp_358_:
{
size_t v___x_360_; size_t v___x_361_; 
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_350_, v___x_360_);
v_i_350_ = v___x_361_;
v_b_352_ = v_a_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object* v_as_383_, lean_object* v_i_384_, lean_object* v_stop_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
size_t v_i_boxed_392_; size_t v_stop_boxed_393_; lean_object* v_res_394_; 
v_i_boxed_392_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_stop_boxed_393_ = lean_unbox_usize(v_stop_385_);
lean_dec(v_stop_385_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7(v_as_383_, v_i_boxed_392_, v_stop_boxed_393_, v_b_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v_as_383_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_env_402_; lean_object* v___x_403_; lean_object* v_mctx_404_; lean_object* v_lctx_405_; lean_object* v_options_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = lean_st_ref_get(v___y_397_);
v_mctx_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_mctx_404_);
lean_dec(v___x_403_);
v_lctx_405_ = lean_ctor_get(v___y_396_, 2);
v_options_406_ = lean_ctor_get(v___y_398_, 2);
lean_inc_ref(v_options_406_);
lean_inc_ref(v_lctx_405_);
v___x_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_407_, 0, v_env_402_);
lean_ctor_set(v___x_407_, 1, v_mctx_404_);
lean_ctor_set(v___x_407_, 2, v_lctx_405_);
lean_ctor_set(v___x_407_, 3, v_options_406_);
v___x_408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_msgData_395_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(lean_object* v_msgData_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_ref_423_; lean_object* v___x_424_; lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_ref_423_ = lean_ctor_get(v___y_420_, 5);
v___x_424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_inc(v_ref_423_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_ref_423_);
lean_ctor_set(v___x_429_, 1, v_a_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 1);
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__0));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__2));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__7));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__9));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__11));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__13));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__15));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__17));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__19));
v___x_472_ = l_Lean_stringToMessageData(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__24));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__28));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__32));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__34));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__36));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__38));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__46(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_box(0);
v___x_511_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__45));
v___x_512_ = l_Lean_mkConst(v___x_511_, v___x_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* v_mvarId_513_, lean_object* v___x_514_, lean_object* v_heq_515_, lean_object* v_e_516_, lean_object* v_config_517_, uint8_t v_symm_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___x_552_; 
lean_inc(v___x_514_);
lean_inc(v_mvarId_513_);
v___x_552_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_513_, v___x_514_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
lean_dec_ref_known(v___x_552_, 1);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc_ref(v_heq_515_);
v___x_553_ = lean_infer_type(v_heq_515_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_1079_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_a_554_, v___y_520_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_1079_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_1079_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(0);
v___x_561_ = 0;
v___x_562_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_556_, v___x_560_, v___x_561_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v_snd_564_; lean_object* v_fst_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_1070_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v_snd_564_ = lean_ctor_get(v_a_563_, 1);
v_fst_565_ = lean_ctor_get(v_a_563_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_a_563_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_567_ = v_a_563_;
v_isShared_568_ = v_isSharedCheck_1070_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_564_);
lean_inc(v_fst_565_);
lean_dec(v_a_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_1070_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_1069_; 
v_fst_569_ = lean_ctor_get(v_snd_564_, 0);
v_snd_570_ = lean_ctor_get(v_snd_564_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_snd_564_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_572_ = v_snd_564_;
v_isShared_573_ = v_isSharedCheck_1069_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_inc(v_fst_569_);
lean_dec(v_snd_564_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_1069_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___y_575_; size_t v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v_a_583_; lean_object* v___y_612_; lean_object* v___y_613_; size_t v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; uint8_t v___y_775_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v_eNew_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_965_; lean_object* v_heq_966_; lean_object* v_heqType_967_; lean_object* v_lhs_968_; lean_object* v_rhs_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v_heq_993_; lean_object* v_heqType_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
lean_inc_ref(v_heq_515_);
v___x_1050_ = l_Lean_mkAppN(v_heq_515_, v_fst_565_);
v___x_1051_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__43));
v___x_1052_ = lean_unsigned_to_nat(2u);
v___x_1053_ = l_Lean_Expr_isAppOfArity(v_snd_570_, v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
v_heq_993_ = v___x_1050_;
v_heqType_994_ = v_snd_570_;
v___y_995_ = v___y_519_;
v___y_996_ = v___y_520_;
v___y_997_ = v___y_521_;
v___y_998_ = v___y_522_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = l_Lean_Expr_appFn_x21(v_snd_570_);
v___x_1055_ = l_Lean_Expr_appArg_x21(v___x_1054_);
lean_dec_ref(v___x_1054_);
v___x_1056_ = l_Lean_Expr_appArg_x21(v_snd_570_);
lean_dec(v_snd_570_);
lean_inc_ref(v___x_1056_);
lean_inc_ref(v___x_1055_);
v___x_1057_ = l_Lean_Meta_mkEq(v___x_1055_, v___x_1056_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__46, &l_Lean_MVarId_rewrite___lam__1___closed__46_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__46);
v___x_1060_ = l_Lean_mkApp3(v___x_1059_, v___x_1055_, v___x_1056_, v___x_1050_);
v_heq_993_ = v___x_1060_;
v_heqType_994_ = v_a_1058_;
v___y_995_ = v___y_519_;
v___y_996_ = v___y_520_;
v___y_997_ = v___y_521_;
v___y_998_ = v___y_522_;
goto v___jp_992_;
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___x_1056_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v___x_1050_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1061_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1057_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1057_);
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
v___jp_574_:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_appendParentTag(v_mvarId_513_, v_fst_565_, v_fst_569_, v___y_577_, v___y_579_, v___y_580_, v___y_582_);
lean_dec(v_fst_569_);
lean_dec(v_fst_565_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_585_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_585_ = l_Lean_Meta_getMVarsNoDelayed(v_heq_515_, v___y_577_, v___y_579_, v___y_580_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_577_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = lean_array_get_size(v_a_586_);
v___x_588_ = lean_mk_empty_array_with_capacity(v___y_575_);
v___x_589_ = lean_nat_dec_lt(v___y_575_, v___x_587_);
if (v___x_589_ == 0)
{
lean_dec(v_a_586_);
v___y_544_ = v_a_583_;
v___y_545_ = v___y_578_;
v___y_546_ = v___y_581_;
v___y_547_ = v___x_588_;
goto v___jp_543_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = lean_nat_dec_le(v___x_587_, v___x_587_);
if (v___x_590_ == 0)
{
if (v___x_589_ == 0)
{
lean_dec(v_a_586_);
v___y_544_ = v_a_583_;
v___y_545_ = v___y_578_;
v___y_546_ = v___y_581_;
v___y_547_ = v___x_588_;
goto v___jp_543_;
}
else
{
size_t v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_usize_of_nat(v___x_587_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_a_583_, v_a_586_, v___y_576_, v___x_591_, v___x_588_);
lean_dec(v_a_586_);
v___y_544_ = v_a_583_;
v___y_545_ = v___y_578_;
v___y_546_ = v___y_581_;
v___y_547_ = v___x_592_;
goto v___jp_543_;
}
}
else
{
size_t v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_usize_of_nat(v___x_587_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_a_583_, v_a_586_, v___y_576_, v___x_593_, v___x_588_);
lean_dec(v_a_586_);
v___y_544_ = v_a_583_;
v___y_545_ = v___y_578_;
v___y_546_ = v___y_581_;
v___y_547_ = v___x_594_;
goto v___jp_543_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_a_583_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v___y_578_);
v_a_595_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_585_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_585_);
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
lean_dec_ref(v_a_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v_heq_515_);
v_a_603_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_584_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_584_);
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
if (lean_obj_tag(v___y_620_) == 0)
{
lean_object* v_a_621_; 
v_a_621_ = lean_ctor_get(v___y_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___y_620_, 1);
v___y_575_ = v___y_612_;
v___y_576_ = v___y_614_;
v___y_577_ = v___y_613_;
v___y_578_ = v___y_615_;
v___y_579_ = v___y_616_;
v___y_580_ = v___y_617_;
v___y_581_ = v___y_618_;
v___y_582_ = v___y_619_;
v_a_583_ = v_a_621_;
goto v___jp_574_;
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v___y_613_);
lean_dec(v_fst_569_);
lean_dec(v_fst_565_);
lean_dec_ref(v_heq_515_);
lean_dec(v_mvarId_513_);
v_a_622_ = lean_ctor_get(v___y_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___y_620_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___y_620_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___y_620_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_642_; 
lean_inc_ref(v___y_636_);
v___x_642_ = l_Lean_Meta_getLevel(v___y_636_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
lean_inc_ref(v___y_633_);
v___x_644_ = l_Lean_Meta_getLevel(v___y_633_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_options_646_; lean_object* v___x_647_; uint8_t v___x_648_; uint8_t v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v_options_646_ = lean_ctor_get(v___y_640_, 2);
v___x_647_ = l_Lean_Meta_tactic_skipAssignedInstances;
v___x_648_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__3(v_options_646_, v___x_647_);
v___x_649_ = lean_bool_not(v___x_648_);
v___x_650_ = 0;
lean_inc(v_fst_569_);
lean_inc(v_mvarId_513_);
v___x_651_ = l_Lean_Meta_postprocessAppMVars(v___x_514_, v_mvarId_513_, v_fst_565_, v_fst_569_, v___x_649_, v___x_650_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_652_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__5));
v___x_653_ = lean_box(0);
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 1);
lean_ctor_set(v___x_572_, 1, v___x_653_);
lean_ctor_set(v___x_572_, 0, v_a_645_);
v___x_655_ = v___x_572_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_645_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_673_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 1, v___x_655_);
lean_ctor_set(v___x_567_, 0, v_a_643_);
v___x_657_ = v___x_567_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_643_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_672_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; size_t v_sz_660_; size_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_658_ = l_Lean_Expr_const___override(v___x_652_, v___x_657_);
v___x_659_ = l_Lean_mkApp6(v___x_658_, v___y_636_, v___y_633_, v___y_635_, v___y_632_, v___y_631_, v___y_634_);
v_sz_660_ = lean_array_size(v_fst_565_);
v___x_661_ = ((size_t)0ULL);
lean_inc(v_fst_565_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__4(v_sz_660_, v___x_661_, v_fst_565_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get_size(v___x_662_);
v___x_665_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_666_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
if (v___x_666_ == 0)
{
lean_dec_ref(v___x_662_);
v___y_575_ = v___x_663_;
v___y_576_ = v___x_661_;
v___y_577_ = v___y_638_;
v___y_578_ = v___x_659_;
v___y_579_ = v___y_639_;
v___y_580_ = v___y_640_;
v___y_581_ = v___y_637_;
v___y_582_ = v___y_641_;
v_a_583_ = v___x_665_;
goto v___jp_574_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_le(v___x_664_, v___x_664_);
if (v___x_667_ == 0)
{
if (v___x_666_ == 0)
{
lean_dec_ref(v___x_662_);
v___y_575_ = v___x_663_;
v___y_576_ = v___x_661_;
v___y_577_ = v___y_638_;
v___y_578_ = v___x_659_;
v___y_579_ = v___y_639_;
v___y_580_ = v___y_640_;
v___y_581_ = v___y_637_;
v___y_582_ = v___y_641_;
v_a_583_ = v___x_665_;
goto v___jp_574_;
}
else
{
size_t v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_usize_of_nat(v___x_664_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7(v___x_662_, v___x_661_, v___x_668_, v___x_665_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec_ref(v___x_662_);
v___y_612_ = v___x_663_;
v___y_613_ = v___y_638_;
v___y_614_ = v___x_661_;
v___y_615_ = v___x_659_;
v___y_616_ = v___y_639_;
v___y_617_ = v___y_640_;
v___y_618_ = v___y_637_;
v___y_619_ = v___y_641_;
v___y_620_ = v___x_669_;
goto v___jp_611_;
}
}
else
{
size_t v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_usize_of_nat(v___x_664_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__7(v___x_662_, v___x_661_, v___x_670_, v___x_665_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec_ref(v___x_662_);
v___y_612_ = v___x_663_;
v___y_613_ = v___y_638_;
v___y_614_ = v___x_661_;
v___y_615_ = v___x_659_;
v___y_616_ = v___y_639_;
v___y_617_ = v___y_640_;
v___y_618_ = v___y_637_;
v___y_619_ = v___y_641_;
v___y_620_ = v___x_671_;
goto v___jp_611_;
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_a_645_);
lean_dec(v_a_643_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_631_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_dec_ref(v_heq_515_);
lean_dec(v_mvarId_513_);
v_a_674_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_651_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_651_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_643_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_631_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_682_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_644_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_644_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_631_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_690_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_642_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_642_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
v___jp_698_:
{
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v___x_714_; 
lean_dec_ref_known(v___y_713_, 1);
lean_inc_ref(v___y_710_);
v___x_714_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v___y_703_, v___y_710_, v___y_702_, v___y_707_, v___y_709_, v___y_700_, v___y_708_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; uint8_t v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_717_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__8, &l_Lean_MVarId_rewrite___lam__1___closed__8_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__8);
lean_inc_ref(v___y_699_);
v___x_718_ = l_Lean_MessageData_ofExpr(v___y_699_);
v___x_719_ = l_Lean_indentD(v___x_718_);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_717_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__10, &l_Lean_MVarId_rewrite___lam__1___closed__10_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__10);
v___x_722_ = l_Lean_indentExpr(v___y_712_);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__12, &l_Lean_MVarId_rewrite___lam__1___closed__12_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__12);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_inc_ref(v___y_705_);
v___x_726_ = l_Lean_indentExpr(v___y_705_);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_MessageData_note(v___x_727_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_720_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 1);
lean_ctor_set(v___x_558_, 0, v___x_729_);
v___x_731_ = v___x_558_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_741_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; 
lean_inc(v_mvarId_513_);
lean_inc(v___x_514_);
v___x_732_ = l_Lean_Meta_throwTacticEx___redArg(v___x_514_, v_mvarId_513_, v___x_731_, v___y_707_, v___y_709_, v___y_700_, v___y_708_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref_known(v___x_732_, 1);
v___y_631_ = v___y_699_;
v___y_632_ = v___y_701_;
v___y_633_ = v___y_704_;
v___y_634_ = v___y_711_;
v___y_635_ = v___y_705_;
v___y_636_ = v___y_710_;
v___y_637_ = v___y_706_;
v___y_638_ = v___y_707_;
v___y_639_ = v___y_709_;
v___y_640_ = v___y_700_;
v___y_641_ = v___y_708_;
goto v___jp_630_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_712_);
lean_del_object(v___x_558_);
v___y_631_ = v___y_699_;
v___y_632_ = v___y_701_;
v___y_633_ = v___y_704_;
v___y_634_ = v___y_711_;
v___y_635_ = v___y_705_;
v___y_636_ = v___y_710_;
v___y_637_ = v___y_706_;
v___y_638_ = v___y_707_;
v___y_639_ = v___y_709_;
v___y_640_ = v___y_700_;
v___y_641_ = v___y_708_;
goto v___jp_630_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_742_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_714_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_714_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___y_699_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_750_ = lean_ctor_get(v___y_713_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___y_713_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___y_713_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___y_713_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
v___jp_758_:
{
if (v___y_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref(v___y_774_);
v___x_776_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__14, &l_Lean_MVarId_rewrite___lam__1___closed__14_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__14);
lean_inc_ref(v___y_759_);
v___x_777_ = l_Lean_MessageData_ofExpr(v___y_759_);
v___x_778_ = l_Lean_indentD(v___x_777_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_776_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__16, &l_Lean_MVarId_rewrite___lam__1___closed__16_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__16);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Lean_Exception_toMessageData(v___y_769_);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__18, &l_Lean_MVarId_rewrite___lam__1___closed__18_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__18);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__5));
v___x_787_ = l_Lean_MessageData_ofConstName(v___x_786_, v___y_775_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_785_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__20, &l_Lean_MVarId_rewrite___lam__1___closed__20_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__20);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__23));
v___x_792_ = l_Lean_MessageData_ofConstName(v___x_791_, v___y_775_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_790_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__25, &l_Lean_MVarId_rewrite___lam__1___closed__25_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__25);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__27));
v___x_797_ = l_Lean_MessageData_ofConstName(v___x_796_, v___y_775_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__29, &l_Lean_MVarId_rewrite___lam__1___closed__29_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__29);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_inc(v_mvarId_513_);
lean_inc(v___x_514_);
v___x_802_ = l_Lean_Meta_throwTacticEx___redArg(v___x_514_, v_mvarId_513_, v___x_801_, v___y_767_, v___y_770_, v___y_760_, v___y_768_);
v___y_699_ = v___y_759_;
v___y_700_ = v___y_760_;
v___y_701_ = v___y_761_;
v___y_702_ = v___y_762_;
v___y_703_ = v___y_763_;
v___y_704_ = v___y_764_;
v___y_705_ = v___y_765_;
v___y_706_ = v___y_766_;
v___y_707_ = v___y_767_;
v___y_708_ = v___y_768_;
v___y_709_ = v___y_770_;
v___y_710_ = v___y_772_;
v___y_711_ = v___y_771_;
v___y_712_ = v___y_773_;
v___y_713_ = v___x_802_;
goto v___jp_698_;
}
else
{
lean_dec_ref(v___y_769_);
v___y_699_ = v___y_759_;
v___y_700_ = v___y_760_;
v___y_701_ = v___y_761_;
v___y_702_ = v___y_762_;
v___y_703_ = v___y_763_;
v___y_704_ = v___y_764_;
v___y_705_ = v___y_765_;
v___y_706_ = v___y_766_;
v___y_707_ = v___y_767_;
v___y_708_ = v___y_768_;
v___y_709_ = v___y_770_;
v___y_710_ = v___y_772_;
v___y_711_ = v___y_771_;
v___y_712_ = v___y_773_;
v___y_713_ = v___y_774_;
goto v___jp_698_;
}
}
v___jp_803_:
{
lean_object* v___x_816_; 
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc_ref(v___y_810_);
v___x_816_ = lean_infer_type(v___y_810_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___f_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_n(v_a_817_, 2);
lean_dec_ref_known(v___x_816_, 1);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(v___f_818_, 0, v___y_804_);
lean_closure_set(v___f_818_, 1, v_a_817_);
v___x_819_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__31));
v___x_820_ = 0;
lean_inc_ref(v___y_809_);
v___x_821_ = l_Lean_mkLambda(v___x_819_, v___x_820_, v___y_809_, v___y_806_);
v___x_822_ = 0;
lean_inc_ref(v___x_821_);
v___x_823_ = l_Lean_Meta_check(v___x_821_, v___x_822_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_823_) == 0)
{
v___y_699_ = v___x_821_;
v___y_700_ = v___y_814_;
v___y_701_ = v___y_805_;
v___y_702_ = v___f_818_;
v___y_703_ = v___x_819_;
v___y_704_ = v_a_817_;
v___y_705_ = v___y_807_;
v___y_706_ = v_eNew_811_;
v___y_707_ = v___y_812_;
v___y_708_ = v___y_815_;
v___y_709_ = v___y_813_;
v___y_710_ = v___y_809_;
v___y_711_ = v___y_808_;
v___y_712_ = v___y_810_;
v___y_713_ = v___x_823_;
goto v___jp_698_;
}
else
{
lean_object* v_a_824_; uint8_t v___x_825_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
v___x_825_ = l_Lean_Exception_isInterrupt(v_a_824_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
lean_inc(v_a_824_);
v___x_826_ = l_Lean_Exception_isRuntime(v_a_824_);
v___y_759_ = v___x_821_;
v___y_760_ = v___y_814_;
v___y_761_ = v___y_805_;
v___y_762_ = v___f_818_;
v___y_763_ = v___x_819_;
v___y_764_ = v_a_817_;
v___y_765_ = v___y_807_;
v___y_766_ = v_eNew_811_;
v___y_767_ = v___y_812_;
v___y_768_ = v___y_815_;
v___y_769_ = v_a_824_;
v___y_770_ = v___y_813_;
v___y_771_ = v___y_808_;
v___y_772_ = v___y_809_;
v___y_773_ = v___y_810_;
v___y_774_ = v___x_823_;
v___y_775_ = v___x_826_;
goto v___jp_758_;
}
else
{
v___y_759_ = v___x_821_;
v___y_760_ = v___y_814_;
v___y_761_ = v___y_805_;
v___y_762_ = v___f_818_;
v___y_763_ = v___x_819_;
v___y_764_ = v_a_817_;
v___y_765_ = v___y_807_;
v___y_766_ = v_eNew_811_;
v___y_767_ = v___y_812_;
v___y_768_ = v___y_815_;
v___y_769_ = v_a_824_;
v___y_770_ = v___y_813_;
v___y_771_ = v___y_808_;
v___y_772_ = v___y_809_;
v___y_773_ = v___y_810_;
v___y_774_ = v___x_823_;
v___y_775_ = v___x_825_;
goto v___jp_758_;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_eNew_811_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v___y_804_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_827_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_816_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_816_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
v___jp_835_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_a_848_; uint8_t v___x_849_; 
v___x_846_ = lean_expr_instantiate1(v___y_836_, v___y_837_);
v___x_847_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v___x_846_, v___y_843_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = l_Lean_Expr_hasBinderNameHint(v___y_837_);
if (v___x_849_ == 0)
{
lean_inc_ref(v___y_836_);
v___y_804_ = v___y_836_;
v___y_805_ = v___y_837_;
v___y_806_ = v___y_836_;
v___y_807_ = v___y_840_;
v___y_808_ = v___y_839_;
v___y_809_ = v___y_838_;
v___y_810_ = v___y_841_;
v_eNew_811_ = v_a_848_;
v___y_812_ = v___y_842_;
v___y_813_ = v___y_843_;
v___y_814_ = v___y_844_;
v___y_815_ = v___y_845_;
goto v___jp_803_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Expr_resolveBinderNameHint(v_a_848_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
lean_inc_ref(v___y_836_);
v___y_804_ = v___y_836_;
v___y_805_ = v___y_837_;
v___y_806_ = v___y_836_;
v___y_807_ = v___y_840_;
v___y_808_ = v___y_839_;
v___y_809_ = v___y_838_;
v___y_810_ = v___y_841_;
v_eNew_811_ = v_a_851_;
v___y_812_ = v___y_842_;
v___y_813_ = v___y_843_;
v___y_814_ = v___y_844_;
v___y_815_ = v___y_845_;
goto v___jp_803_;
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec_ref(v___y_836_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_852_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_850_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
v___jp_860_:
{
lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_963_; 
v___x_869_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_516_, v___y_866_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_963_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_963_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_963_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v_transparency_874_; uint8_t v_offsetCnstrs_875_; lean_object* v_occs_876_; lean_object* v___x_877_; uint8_t v_foApprox_878_; uint8_t v_ctxApprox_879_; uint8_t v_quasiPatternApprox_880_; uint8_t v_constApprox_881_; uint8_t v_isDefEqStuckEx_882_; uint8_t v_unificationHints_883_; uint8_t v_proofIrrelevance_884_; uint8_t v_assignSyntheticOpaque_885_; uint8_t v_etaStruct_886_; uint8_t v_univApprox_887_; uint8_t v_iota_888_; uint8_t v_beta_889_; uint8_t v_proj_890_; uint8_t v_zeta_891_; uint8_t v_zetaDelta_892_; uint8_t v_zetaUnused_893_; uint8_t v_zetaHave_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_962_; 
v_transparency_874_ = lean_ctor_get_uint8(v_config_517_, sizeof(void*)*1);
v_offsetCnstrs_875_ = lean_ctor_get_uint8(v_config_517_, sizeof(void*)*1 + 1);
v_occs_876_ = lean_ctor_get(v_config_517_, 0);
lean_inc(v_occs_876_);
lean_dec_ref(v_config_517_);
v___x_877_ = l_Lean_Meta_Context_config(v___y_865_);
v_foApprox_878_ = lean_ctor_get_uint8(v___x_877_, 0);
v_ctxApprox_879_ = lean_ctor_get_uint8(v___x_877_, 1);
v_quasiPatternApprox_880_ = lean_ctor_get_uint8(v___x_877_, 2);
v_constApprox_881_ = lean_ctor_get_uint8(v___x_877_, 3);
v_isDefEqStuckEx_882_ = lean_ctor_get_uint8(v___x_877_, 4);
v_unificationHints_883_ = lean_ctor_get_uint8(v___x_877_, 5);
v_proofIrrelevance_884_ = lean_ctor_get_uint8(v___x_877_, 6);
v_assignSyntheticOpaque_885_ = lean_ctor_get_uint8(v___x_877_, 7);
v_etaStruct_886_ = lean_ctor_get_uint8(v___x_877_, 10);
v_univApprox_887_ = lean_ctor_get_uint8(v___x_877_, 11);
v_iota_888_ = lean_ctor_get_uint8(v___x_877_, 12);
v_beta_889_ = lean_ctor_get_uint8(v___x_877_, 13);
v_proj_890_ = lean_ctor_get_uint8(v___x_877_, 14);
v_zeta_891_ = lean_ctor_get_uint8(v___x_877_, 15);
v_zetaDelta_892_ = lean_ctor_get_uint8(v___x_877_, 16);
v_zetaUnused_893_ = lean_ctor_get_uint8(v___x_877_, 17);
v_zetaHave_894_ = lean_ctor_get_uint8(v___x_877_, 18);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_962_ == 0)
{
v___x_896_ = v___x_877_;
v_isShared_897_ = v_isSharedCheck_962_;
goto v_resetjp_895_;
}
else
{
lean_dec(v___x_877_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_962_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
uint8_t v_trackZetaDelta_898_; lean_object* v_zetaDeltaSet_899_; lean_object* v_lctx_900_; lean_object* v_localInstances_901_; lean_object* v_defEqCtx_x3f_902_; lean_object* v_synthPendingDepth_903_; lean_object* v_canUnfold_x3f_904_; uint8_t v_univApprox_905_; uint8_t v_inTypeClassResolution_906_; uint8_t v_cacheInferType_907_; lean_object* v___x_909_; 
v_trackZetaDelta_898_ = lean_ctor_get_uint8(v___y_865_, sizeof(void*)*7);
v_zetaDeltaSet_899_ = lean_ctor_get(v___y_865_, 1);
v_lctx_900_ = lean_ctor_get(v___y_865_, 2);
v_localInstances_901_ = lean_ctor_get(v___y_865_, 3);
v_defEqCtx_x3f_902_ = lean_ctor_get(v___y_865_, 4);
v_synthPendingDepth_903_ = lean_ctor_get(v___y_865_, 5);
v_canUnfold_x3f_904_ = lean_ctor_get(v___y_865_, 6);
v_univApprox_905_ = lean_ctor_get_uint8(v___y_865_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_906_ = lean_ctor_get_uint8(v___y_865_, sizeof(void*)*7 + 2);
v_cacheInferType_907_ = lean_ctor_get_uint8(v___y_865_, sizeof(void*)*7 + 3);
if (v_isShared_897_ == 0)
{
v___x_909_ = v___x_896_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 0, v_foApprox_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 1, v_ctxApprox_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 2, v_quasiPatternApprox_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 3, v_constApprox_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 4, v_isDefEqStuckEx_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 5, v_unificationHints_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 6, v_proofIrrelevance_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 7, v_assignSyntheticOpaque_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 10, v_etaStruct_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 11, v_univApprox_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 12, v_iota_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 13, v_beta_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 14, v_proj_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 15, v_zeta_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 16, v_zetaDelta_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 17, v_zetaUnused_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, 18, v_zetaHave_894_);
v___x_909_ = v_reuseFailAlloc_961_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
uint64_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_ctor_set_uint8(v___x_909_, 8, v_offsetCnstrs_875_);
lean_ctor_set_uint8(v___x_909_, 9, v_transparency_874_);
v___x_910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set_uint64(v___x_911_, sizeof(void*)*1, v___x_910_);
lean_inc(v_canUnfold_x3f_904_);
lean_inc(v_synthPendingDepth_903_);
lean_inc(v_defEqCtx_x3f_902_);
lean_inc_ref(v_localInstances_901_);
lean_inc_ref(v_lctx_900_);
lean_inc(v_zetaDeltaSet_899_);
v___x_912_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_zetaDeltaSet_899_);
lean_ctor_set(v___x_912_, 2, v_lctx_900_);
lean_ctor_set(v___x_912_, 3, v_localInstances_901_);
lean_ctor_set(v___x_912_, 4, v_defEqCtx_x3f_902_);
lean_ctor_set(v___x_912_, 5, v_synthPendingDepth_903_);
lean_ctor_set(v___x_912_, 6, v_canUnfold_x3f_904_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7, v_trackZetaDelta_898_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 1, v_univApprox_905_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 2, v_inTypeClassResolution_906_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 3, v_cacheInferType_907_);
lean_inc_ref(v___y_864_);
lean_inc(v_a_870_);
v___x_913_ = l_Lean_Meta_kabstract(v_a_870_, v___y_864_, v_occs_876_, v___x_912_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref_known(v___x_912_, 7);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; uint8_t v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Expr_hasLooseBVars(v_a_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_inc_ref(v___y_864_);
lean_inc(v_a_870_);
v___x_916_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_870_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v_fst_918_; lean_object* v_snd_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_944_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v_fst_918_ = lean_ctor_get(v_a_917_, 0);
v_snd_919_ = lean_ctor_get(v_a_917_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_917_);
if (v_isSharedCheck_944_ == 0)
{
v___x_921_ = v_a_917_;
v_isShared_922_ = v_isSharedCheck_944_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_snd_919_);
lean_inc(v_fst_918_);
lean_dec(v_a_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_944_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__33, &l_Lean_MVarId_rewrite___lam__1___closed__33_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__33);
v___x_924_ = l_Lean_indentExpr(v_snd_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 7);
lean_ctor_set(v___x_921_, 1, v___x_924_);
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_943_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_927_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__35, &l_Lean_MVarId_rewrite___lam__1___closed__35_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__35);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_indentExpr(v_fst_918_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 1);
lean_ctor_set(v___x_872_, 0, v___x_930_);
v___x_932_ = v___x_872_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_942_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
lean_inc(v_mvarId_513_);
lean_inc(v___x_514_);
v___x_933_ = l_Lean_Meta_throwTacticEx___redArg(v___x_514_, v_mvarId_513_, v___x_932_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_dec_ref_known(v___x_933_, 1);
v___y_836_ = v_a_914_;
v___y_837_ = v___y_861_;
v___y_838_ = v___y_862_;
v___y_839_ = v___y_863_;
v___y_840_ = v___y_864_;
v___y_841_ = v_a_870_;
v___y_842_ = v___y_865_;
v___y_843_ = v___y_866_;
v___y_844_ = v___y_867_;
v___y_845_ = v___y_868_;
goto v___jp_835_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_914_);
lean_dec(v_a_870_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___y_861_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
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
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_914_);
lean_del_object(v___x_872_);
lean_dec(v_a_870_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___y_861_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_945_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_916_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_916_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_del_object(v___x_872_);
v___y_836_ = v_a_914_;
v___y_837_ = v___y_861_;
v___y_838_ = v___y_862_;
v___y_839_ = v___y_863_;
v___y_840_ = v___y_864_;
v___y_841_ = v_a_870_;
v___y_842_ = v___y_865_;
v___y_843_ = v___y_866_;
v___y_844_ = v___y_867_;
v___y_845_ = v___y_868_;
goto v___jp_835_;
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_del_object(v___x_872_);
lean_dec(v_a_870_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___y_861_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_953_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_913_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_913_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
}
v___jp_964_:
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = l_Lean_Expr_getAppFn(v_lhs_968_);
v___x_975_ = l_Lean_Expr_isMVar(v___x_974_);
lean_dec_ref(v___x_974_);
if (v___x_975_ == 0)
{
lean_dec_ref(v_heqType_967_);
v___y_861_ = v_rhs_969_;
v___y_862_ = v___y_965_;
v___y_863_ = v_heq_966_;
v___y_864_ = v_lhs_968_;
v___y_865_ = v___y_970_;
v___y_866_ = v___y_971_;
v___y_867_ = v___y_972_;
v___y_868_ = v___y_973_;
goto v___jp_860_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_rhs_969_);
lean_dec_ref(v_heq_966_);
lean_dec_ref(v___y_965_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v___x_976_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__37, &l_Lean_MVarId_rewrite___lam__1___closed__37_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__37);
v___x_977_ = l_Lean_MessageData_ofExpr(v_lhs_968_);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__39, &l_Lean_MVarId_rewrite___lam__1___closed__39_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__39);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_indentExpr(v_heqType_967_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_982_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
v___jp_992_:
{
lean_object* v___x_999_; 
lean_inc_ref(v_heqType_994_);
v___x_999_ = l_Lean_Meta_matchEq_x3f(v_heqType_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
if (lean_obj_tag(v_a_1000_) == 0)
{
lean_object* v___x_1001_; 
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
lean_inc_ref(v_heqType_994_);
v___x_1001_ = l_Lean_Meta_isProp(v_heqType_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; uint8_t v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = lean_unbox(v_a_1002_);
lean_dec(v_a_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__40));
v___y_525_ = v___y_998_;
v___y_526_ = v_heq_993_;
v___y_527_ = v___y_997_;
v___y_528_ = v___y_996_;
v___y_529_ = v___y_995_;
v___y_530_ = v_heqType_994_;
v___y_531_ = v___x_1004_;
goto v___jp_524_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__41));
v___y_525_ = v___y_998_;
v___y_526_ = v_heq_993_;
v___y_527_ = v___y_997_;
v___y_528_ = v___y_996_;
v___y_529_ = v___y_995_;
v___y_530_ = v_heqType_994_;
v___y_531_ = v___x_1005_;
goto v___jp_524_;
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_heqType_994_);
lean_dec_ref(v_heq_993_);
v_a_1006_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1001_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1001_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_val_1014_; lean_object* v_snd_1015_; 
v_val_1014_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v_a_1000_, 1);
v_snd_1015_ = lean_ctor_get(v_val_1014_, 1);
lean_inc(v_snd_1015_);
if (v_symm_518_ == 0)
{
lean_object* v_fst_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; 
v_fst_1016_ = lean_ctor_get(v_val_1014_, 0);
lean_inc(v_fst_1016_);
lean_dec(v_val_1014_);
v_fst_1017_ = lean_ctor_get(v_snd_1015_, 0);
lean_inc(v_fst_1017_);
v_snd_1018_ = lean_ctor_get(v_snd_1015_, 1);
lean_inc(v_snd_1018_);
lean_dec(v_snd_1015_);
v___y_965_ = v_fst_1016_;
v_heq_966_ = v_heq_993_;
v_heqType_967_ = v_heqType_994_;
v_lhs_968_ = v_fst_1017_;
v_rhs_969_ = v_snd_1018_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_996_;
v___y_972_ = v___y_997_;
v___y_973_ = v___y_998_;
goto v___jp_964_;
}
else
{
lean_object* v_fst_1019_; lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v_heqType_994_);
v_fst_1019_ = lean_ctor_get(v_val_1014_, 0);
lean_inc(v_fst_1019_);
lean_dec(v_val_1014_);
v_fst_1020_ = lean_ctor_get(v_snd_1015_, 0);
lean_inc(v_fst_1020_);
v_snd_1021_ = lean_ctor_get(v_snd_1015_, 1);
lean_inc(v_snd_1021_);
lean_dec(v_snd_1015_);
v___x_1022_ = l_Lean_Meta_mkEqSymm(v_heq_993_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
lean_inc(v_fst_1020_);
lean_inc(v_snd_1021_);
v___x_1024_ = l_Lean_Meta_mkEq(v_snd_1021_, v_fst_1020_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___y_965_ = v_fst_1019_;
v_heq_966_ = v_a_1023_;
v_heqType_967_ = v_a_1025_;
v_lhs_968_ = v_snd_1021_;
v_rhs_969_ = v_fst_1020_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_996_;
v___y_972_ = v___y_997_;
v___y_973_ = v___y_998_;
goto v___jp_964_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_1023_);
lean_dec(v_snd_1021_);
lean_dec(v_fst_1020_);
lean_dec(v_fst_1019_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1026_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_snd_1021_);
lean_dec(v_fst_1020_);
lean_dec(v_fst_1019_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1034_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1022_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1022_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_heqType_994_);
lean_dec_ref(v_heq_993_);
lean_del_object(v___x_572_);
lean_dec(v_fst_569_);
lean_del_object(v___x_567_);
lean_dec(v_fst_565_);
lean_del_object(v___x_558_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1042_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_999_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_999_);
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
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_558_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1071_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_562_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_562_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1080_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_553_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_553_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
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
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_config_517_);
lean_dec_ref(v_e_516_);
lean_dec_ref(v_heq_515_);
lean_dec(v___x_514_);
lean_dec(v_mvarId_513_);
v_a_1088_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_552_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_552_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
v___jp_524_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_532_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__1, &l_Lean_MVarId_rewrite___lam__1___closed__1_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__1);
v___x_533_ = lean_unsigned_to_nat(30u);
v___x_534_ = l_Lean_inlineExpr(v___y_526_, v___x_533_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_532_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__3, &l_Lean_MVarId_rewrite___lam__1___closed__3_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__3);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc_ref(v___y_531_);
v___x_538_ = l_Lean_stringToMessageData(v___y_531_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_indentExpr(v___y_530_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_541_, v___y_529_, v___y_528_, v___y_527_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_529_);
return v___x_542_;
}
v___jp_543_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = l_Array_append___redArg(v___y_544_, v___y_547_);
lean_dec_ref(v___y_547_);
v___x_549_ = lean_array_to_list(v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v___y_546_);
lean_ctor_set(v___x_550_, 1, v___y_545_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* v_mvarId_1096_, lean_object* v___x_1097_, lean_object* v_heq_1098_, lean_object* v_e_1099_, lean_object* v_config_1100_, lean_object* v_symm_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
uint8_t v_symm_boxed_1107_; lean_object* v_res_1108_; 
v_symm_boxed_1107_ = lean_unbox(v_symm_1101_);
v_res_1108_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_1096_, v___x_1097_, v_heq_1098_, v_e_1099_, v_config_1100_, v_symm_boxed_1107_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* v_mvarId_1112_, lean_object* v_e_1113_, lean_object* v_heq_1114_, uint8_t v_symm_1115_, lean_object* v_config_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; 
v___x_1122_ = ((lean_object*)(l_Lean_MVarId_rewrite___closed__1));
v___x_1123_ = lean_box(v_symm_1115_);
lean_inc(v_mvarId_1112_);
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1124_, 0, v_mvarId_1112_);
lean_closure_set(v___f_1124_, 1, v___x_1122_);
lean_closure_set(v___f_1124_, 2, v_heq_1114_);
lean_closure_set(v___f_1124_, 3, v_e_1113_);
lean_closure_set(v___f_1124_, 4, v_config_1116_);
lean_closure_set(v___f_1124_, 5, v___x_1123_);
v___x_1125_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_1112_, v___f_1124_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* v_mvarId_1126_, lean_object* v_e_1127_, lean_object* v_heq_1128_, lean_object* v_symm_1129_, lean_object* v_config_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
uint8_t v_symm_boxed_1136_; lean_object* v_res_1137_; 
v_symm_boxed_1136_ = lean_unbox(v_symm_1129_);
v_res_1137_ = l_Lean_MVarId_rewrite(v_mvarId_1126_, v_e_1127_, v_heq_1128_, v_symm_boxed_1136_, v_config_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* v_mvarId_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_1138_, v___y_1140_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* v_mvarId_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v_mvarId_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object* v_00_u03b1_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(v_00_u03b1_1160_, v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_object* v_00_u03b1_1168_, lean_object* v_name_1169_, uint8_t v_bi_1170_, lean_object* v_type_1171_, lean_object* v_k_1172_, uint8_t v_kind_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1169_, v_bi_1170_, v_type_1171_, v_k_1172_, v_kind_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_name_1181_, lean_object* v_bi_1182_, lean_object* v_type_1183_, lean_object* v_k_1184_, lean_object* v_kind_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
uint8_t v_bi_boxed_1191_; uint8_t v_kind_boxed_1192_; lean_object* v_res_1193_; 
v_bi_boxed_1191_ = lean_unbox(v_bi_1182_);
v_kind_boxed_1192_ = lean_unbox(v_kind_1185_);
v_res_1193_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(v_00_u03b1_1180_, v_name_1181_, v_bi_boxed_1191_, v_type_1183_, v_k_1184_, v_kind_boxed_1192_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_object* v_00_u03b1_1194_, lean_object* v_name_1195_, lean_object* v_type_1196_, lean_object* v_k_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_1195_, v_type_1196_, v_k_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* v_00_u03b1_1204_, lean_object* v_name_1205_, lean_object* v_type_1206_, lean_object* v_k_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(v_00_u03b1_1204_, v_name_1205_, v_type_1206_, v_k_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1213_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* v_00_u03b2_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1215_, v_x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_1218_, v_x_1219_, v_x_1220_);
lean_dec(v_x_1220_);
lean_dec_ref(v_x_1219_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1223_, lean_object* v_x_1224_, size_t v_x_1225_, lean_object* v_x_1226_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1224_, v_x_1225_, v_x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1228_, lean_object* v_x_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_){
_start:
{
size_t v_x_19766__boxed_1232_; uint8_t v_res_1233_; lean_object* v_r_1234_; 
v_x_19766__boxed_1232_ = lean_unbox_usize(v_x_1230_);
lean_dec(v_x_1230_);
v_res_1233_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_1228_, v_x_1229_, v_x_19766__boxed_1232_, v_x_1231_);
lean_dec(v_x_1231_);
lean_dec_ref(v_x_1229_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_object* v_00_u03b2_1235_, lean_object* v_keys_1236_, lean_object* v_vals_1237_, lean_object* v_heq_1238_, lean_object* v_i_1239_, lean_object* v_k_1240_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_1236_, v_i_1239_, v_k_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(lean_object* v_00_u03b2_1242_, lean_object* v_keys_1243_, lean_object* v_vals_1244_, lean_object* v_heq_1245_, lean_object* v_i_1246_, lean_object* v_k_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(v_00_u03b2_1242_, v_keys_1243_, v_vals_1244_, v_heq_1245_, v_i_1246_, v_k_1247_);
lean_dec(v_k_1247_);
lean_dec_ref(v_vals_1244_);
lean_dec_ref(v_keys_1243_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_BinderNameHint(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
