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
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
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
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(lean_object* v_opts_46_, lean_object* v_opt_47_){
_start:
{
lean_object* v_name_48_; lean_object* v_defValue_49_; lean_object* v_map_50_; lean_object* v___x_51_; 
v_name_48_ = lean_ctor_get(v_opt_47_, 0);
v_defValue_49_ = lean_ctor_get(v_opt_47_, 1);
v_map_50_ = lean_ctor_get(v_opts_46_, 0);
v___x_51_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_50_, v_name_48_);
if (lean_obj_tag(v___x_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = lean_unbox(v_defValue_49_);
return v___x_52_;
}
else
{
lean_object* v_val_53_; 
v_val_53_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v___x_51_, 1);
if (lean_obj_tag(v_val_53_) == 1)
{
uint8_t v_v_54_; 
v_v_54_ = lean_ctor_get_uint8(v_val_53_, 0);
lean_dec_ref_known(v_val_53_, 0);
return v_v_54_;
}
else
{
uint8_t v___x_55_; 
lean_dec(v_val_53_);
v___x_55_ = lean_unbox(v_defValue_49_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_46_ = stack[0].m_obj;
lean_object* v_opt_47_ = stack[1].m_obj;
uint8_t v_res_56_;
v_res_56_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v_opts_46_, v_opt_47_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7___boxed(lean_object* v_opts_57_, lean_object* v_opt_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v_opts_57_, v_opt_58_);
lean_dec_ref(v_opt_58_);
lean_dec_ref(v_opts_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(lean_object* v_mvarId_61_, lean_object* v_x_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_61_, v_x_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_a_77_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_68_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_68_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_61_ = stack[0].m_obj;
lean_object* v_x_62_ = stack[1].m_obj;
lean_object* v___y_63_ = stack[2].m_obj;
lean_object* v___y_64_ = stack[3].m_obj;
lean_object* v___y_65_ = stack[4].m_obj;
lean_object* v___y_66_ = stack[5].m_obj;
lean_object* v_res_85_;
v_res_85_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_61_, v_x_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg___boxed(lean_object* v_mvarId_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(lean_object* v_00_u03b1_94_, lean_object* v_mvarId_95_, lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_95_, v_x_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_95_ = stack[1].m_obj;
lean_object* v_x_96_ = stack[2].m_obj;
lean_object* v___y_97_ = stack[3].m_obj;
lean_object* v___y_98_ = stack[4].m_obj;
lean_object* v___y_99_ = stack[5].m_obj;
lean_object* v___y_100_ = stack[6].m_obj;
lean_object* v_res_103_;
v_res_103_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(lean_box(0), v_mvarId_95_, v_x_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___boxed(lean_object* v_00_u03b1_104_, lean_object* v_mvarId_105_, lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(v_00_u03b1_104_, v_mvarId_105_, v_x_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_expr_instantiate1(v_a_113_, v_a_115_);
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
v___x_122_ = lean_infer_type(v___x_121_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = l_Lean_Meta_isExprDefEq(v_a_123_, v_a_114_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_a_114_);
v_a_125_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_122_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_rewrite___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_113_ = stack[0].m_obj;
lean_object* v_a_114_ = stack[1].m_obj;
lean_object* v_a_115_ = stack[2].m_obj;
lean_object* v___y_116_ = stack[3].m_obj;
lean_object* v___y_117_ = stack[4].m_obj;
lean_object* v___y_118_ = stack[5].m_obj;
lean_object* v___y_119_ = stack[6].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_MVarId_rewrite___lam__0(v_a_113_, v_a_114_, v_a_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_MVarId_rewrite___lam__0(v_a_134_, v_a_135_, v_a_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec_ref(v_a_136_);
lean_dec_ref(v_a_134_);
return v_res_142_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(size_t v_sz_143_, size_t v_i_144_, lean_object* v_bs_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_lt(v_i_144_, v_sz_143_);
if (v___x_146_ == 0)
{
return v_bs_145_;
}
else
{
lean_object* v_v_147_; lean_object* v___x_148_; lean_object* v_bs_x27_149_; lean_object* v___x_150_; size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v_v_147_ = lean_array_uget(v_bs_145_, v_i_144_);
v___x_148_ = lean_unsigned_to_nat(0u);
v_bs_x27_149_ = lean_array_uset(v_bs_145_, v_i_144_, v___x_148_);
v___x_150_ = l_Lean_Expr_mvarId_x21(v_v_147_);
lean_dec(v_v_147_);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_add(v_i_144_, v___x_151_);
v___x_153_ = lean_array_uset(v_bs_x27_149_, v_i_144_, v___x_150_);
v_i_144_ = v___x_152_;
v_bs_145_ = v___x_153_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_143_ = stack[0].m_num;
size_t v_i_144_ = stack[1].m_num;
lean_object* v_bs_145_ = stack[2].m_obj;
lean_object* v_res_155_;
v_res_155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_143_, v_i_144_, v_bs_145_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3___boxed(lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_bs_158_){
_start:
{
size_t v_sz_boxed_159_; size_t v_i_boxed_160_; lean_object* v_res_161_; 
v_sz_boxed_159_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_boxed_159_, v_i_boxed_160_, v_bs_158_);
return v_res_161_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(lean_object* v_keys_162_, lean_object* v_i_163_, lean_object* v_k_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_array_get_size(v_keys_162_);
v___x_166_ = lean_nat_dec_lt(v_i_163_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_i_163_);
return v___x_166_;
}
else
{
lean_object* v_k_x27_167_; uint8_t v___x_168_; 
v_k_x27_167_ = lean_array_fget_borrowed(v_keys_162_, v_i_163_);
v___x_168_ = l_Lean_instBEqMVarId_beq(v_k_164_, v_k_x27_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_i_163_, v___x_169_);
lean_dec(v_i_163_);
v_i_163_ = v___x_170_;
goto _start;
}
else
{
lean_dec(v_i_163_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_162_ = stack[0].m_obj;
lean_object* v_i_163_ = stack[1].m_obj;
lean_object* v_k_164_ = stack[2].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_162_, v_i_163_, v_k_164_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg___boxed(lean_object* v_keys_173_, lean_object* v_i_174_, lean_object* v_k_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_173_, v_i_174_, v_k_175_);
lean_dec(v_k_175_);
lean_dec_ref(v_keys_173_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object* v_x_178_, size_t v_x_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v_es_181_; lean_object* v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v_j_185_; lean_object* v___x_186_; 
v_es_181_ = lean_ctor_get(v_x_178_, 0);
v___x_182_ = lean_box(2);
v___x_183_ = ((size_t)31ULL);
v___x_184_ = lean_usize_land(v_x_179_, v___x_183_);
v_j_185_ = lean_usize_to_nat(v___x_184_);
v___x_186_ = lean_array_get_borrowed(v___x_182_, v_es_181_, v_j_185_);
lean_dec(v_j_185_);
switch(lean_obj_tag(v___x_186_))
{
case 0:
{
lean_object* v_key_187_; uint8_t v___x_188_; 
v_key_187_ = lean_ctor_get(v___x_186_, 0);
v___x_188_ = l_Lean_instBEqMVarId_beq(v_x_180_, v_key_187_);
return v___x_188_;
}
case 1:
{
lean_object* v_node_189_; size_t v___x_190_; size_t v___x_191_; 
v_node_189_ = lean_ctor_get(v___x_186_, 0);
v___x_190_ = ((size_t)5ULL);
v___x_191_ = lean_usize_shift_right(v_x_179_, v___x_190_);
v_x_178_ = v_node_189_;
v_x_179_ = v___x_191_;
goto _start;
}
default: 
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
}
else
{
lean_object* v_ks_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_ks_194_ = lean_ctor_get(v_x_178_, 0);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_ks_194_, v___x_195_, v_x_180_);
return v___x_196_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_178_ = stack[0].m_obj;
size_t v_x_179_ = stack[1].m_num;
lean_object* v_x_180_ = stack[2].m_obj;
uint8_t v_res_197_;
v_res_197_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_178_, v_x_179_, v_x_180_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
size_t v_x_18260__boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_x_18260__boxed_201_ = lean_unbox_usize(v_x_199_);
lean_dec(v_x_199_);
v_res_202_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_198_, v_x_18260__boxed_201_, v_x_200_);
lean_dec(v_x_200_);
lean_dec_ref(v_x_198_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint64_t v___x_206_; size_t v___x_207_; uint8_t v___x_208_; 
v___x_206_ = l_Lean_instHashableMVarId_hash(v_x_205_);
v___x_207_ = lean_uint64_to_usize(v___x_206_);
v___x_208_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_204_, v___x_207_, v_x_205_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_204_ = stack[0].m_obj;
lean_object* v_x_205_ = stack[1].m_obj;
uint8_t v_res_209_;
v_res_209_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_204_, v_x_205_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_210_, v_x_211_);
lean_dec(v_x_211_);
lean_dec_ref(v_x_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object* v_mvarId_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v_mctx_218_; lean_object* v_eAssignment_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_217_ = lean_st_ref_get(v___y_215_);
v_mctx_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_ref(v_mctx_218_);
lean_dec(v___x_217_);
v_eAssignment_219_ = lean_ctor_get(v_mctx_218_, 8);
lean_inc_ref(v_eAssignment_219_);
lean_dec_ref(v_mctx_218_);
v___x_220_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_eAssignment_219_, v_mvarId_214_);
lean_dec_ref(v_eAssignment_219_);
v___x_221_ = lean_box(v___x_220_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_214_ = stack[0].m_obj;
lean_object* v___y_215_ = stack[1].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_214_, v___y_215_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* v_mvarId_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec(v_mvarId_224_);
return v_res_227_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object* v_as_228_, size_t v_i_229_, size_t v_stop_230_, lean_object* v_b_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_a_238_; uint8_t v___x_242_; 
v___x_242_ = lean_usize_dec_eq(v_i_229_, v_stop_230_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_246_; 
v___x_243_ = lean_array_uget_borrowed(v_as_228_, v_i_229_);
v___x_246_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v___x_243_, v___y_233_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; uint8_t v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = lean_unbox(v_a_247_);
lean_dec(v_a_247_);
if (v___x_248_ == 0)
{
goto v___jp_244_;
}
else
{
v_a_238_ = v_b_231_;
goto v___jp_237_;
}
}
else
{
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_249_; uint8_t v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_246_, 1);
v___x_250_ = lean_unbox(v_a_249_);
lean_dec(v_a_249_);
if (v___x_250_ == 0)
{
v_a_238_ = v_b_231_;
goto v___jp_237_;
}
else
{
goto v___jp_244_;
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v_b_231_);
v_a_251_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_246_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_246_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
v___jp_244_:
{
lean_object* v___x_245_; 
lean_inc(v___x_243_);
v___x_245_ = lean_array_push(v_b_231_, v___x_243_);
v_a_238_ = v___x_245_;
goto v___jp_237_;
}
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_b_231_);
return v___x_259_;
}
v___jp_237_:
{
size_t v___x_239_; size_t v___x_240_; 
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_229_, v___x_239_);
v_i_229_ = v___x_240_;
v_b_231_ = v_a_238_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_228_ = stack[0].m_obj;
size_t v_i_229_ = stack[1].m_num;
size_t v_stop_230_ = stack[2].m_num;
lean_object* v_b_231_ = stack[3].m_obj;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v___y_233_ = stack[5].m_obj;
lean_object* v___y_234_ = stack[6].m_obj;
lean_object* v___y_235_ = stack[7].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_228_, v_i_229_, v_stop_230_, v_b_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object* v_as_261_, lean_object* v_i_262_, lean_object* v_stop_263_, lean_object* v_b_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
size_t v_i_boxed_270_; size_t v_stop_boxed_271_; lean_object* v_res_272_; 
v_i_boxed_270_ = lean_unbox_usize(v_i_262_);
lean_dec(v_i_262_);
v_stop_boxed_271_ = lean_unbox_usize(v_stop_263_);
lean_dec(v_stop_263_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_261_, v_i_boxed_270_, v_stop_boxed_271_, v_b_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_as_261_);
return v_res_272_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object* v_k_273_, lean_object* v_b_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc_ref(v___y_275_);
v___x_280_ = lean_apply_6(v_k_273_, v_b_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, lean_box(0));
return v___x_280_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_273_ = stack[0].m_obj;
lean_object* v_b_274_ = stack[1].m_obj;
lean_object* v___y_275_ = stack[2].m_obj;
lean_object* v___y_276_ = stack[3].m_obj;
lean_object* v___y_277_ = stack[4].m_obj;
lean_object* v___y_278_ = stack[5].m_obj;
lean_object* v_res_281_;
v_res_281_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_273_, v_b_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_k_282_, lean_object* v_b_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_282_, v_b_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object* v_name_290_, uint8_t v_bi_291_, lean_object* v_type_292_, lean_object* v_k_293_, uint8_t v_kind_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; 
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_300_, 0, v_k_293_);
v___x_301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_290_, v_bi_291_, v_type_292_, v___f_300_, v_kind_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_301_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_301_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_290_ = stack[0].m_obj;
uint8_t v_bi_291_ = stack[1].m_num;
lean_object* v_type_292_ = stack[2].m_obj;
lean_object* v_k_293_ = stack[3].m_obj;
uint8_t v_kind_294_ = stack[4].m_num;
lean_object* v___y_295_ = stack[5].m_obj;
lean_object* v___y_296_ = stack[6].m_obj;
lean_object* v___y_297_ = stack[7].m_obj;
lean_object* v___y_298_ = stack[8].m_obj;
lean_object* v_res_318_;
v_res_318_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_290_, v_bi_291_, v_type_292_, v_k_293_, v_kind_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object* v_name_319_, lean_object* v_bi_320_, lean_object* v_type_321_, lean_object* v_k_322_, lean_object* v_kind_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v_bi_boxed_329_; uint8_t v_kind_boxed_330_; lean_object* v_res_331_; 
v_bi_boxed_329_ = lean_unbox(v_bi_320_);
v_kind_boxed_330_ = lean_unbox(v_kind_323_);
v_res_331_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_319_, v_bi_boxed_329_, v_type_321_, v_k_322_, v_kind_boxed_330_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_331_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object* v_name_332_, lean_object* v_type_333_, lean_object* v_k_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = 0;
v___x_341_ = 0;
v___x_342_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_332_, v___x_340_, v_type_333_, v_k_334_, v___x_341_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_342_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_332_ = stack[0].m_obj;
lean_object* v_type_333_ = stack[1].m_obj;
lean_object* v_k_334_ = stack[2].m_obj;
lean_object* v___y_335_ = stack[3].m_obj;
lean_object* v___y_336_ = stack[4].m_obj;
lean_object* v___y_337_ = stack[5].m_obj;
lean_object* v___y_338_ = stack[6].m_obj;
lean_object* v_res_343_;
v_res_343_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_332_, v_type_333_, v_k_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object* v_name_344_, lean_object* v_type_345_, lean_object* v_k_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_344_, v_type_345_, v_k_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_352_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(lean_object* v_a_353_, lean_object* v_as_354_, size_t v_i_355_, size_t v_stop_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_eq(v_i_355_, v_stop_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_array_uget_borrowed(v_as_354_, v_i_355_);
v___x_359_ = l_Lean_instBEqMVarId_beq(v_a_353_, v___x_358_);
if (v___x_359_ == 0)
{
size_t v___x_360_; size_t v___x_361_; 
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_355_, v___x_360_);
v_i_355_ = v___x_361_;
goto _start;
}
else
{
return v___x_359_;
}
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_353_ = stack[0].m_obj;
lean_object* v_as_354_ = stack[1].m_obj;
size_t v_i_355_ = stack[2].m_num;
size_t v_stop_356_ = stack[3].m_num;
uint8_t v_res_364_;
v_res_364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_353_, v_as_354_, v_i_355_, v_stop_356_);
stack->m_num = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6___boxed(lean_object* v_a_365_, lean_object* v_as_366_, lean_object* v_i_367_, lean_object* v_stop_368_){
_start:
{
size_t v_i_boxed_369_; size_t v_stop_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v_i_boxed_369_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_stop_boxed_370_ = lean_unbox_usize(v_stop_368_);
lean_dec(v_stop_368_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_365_, v_as_366_, v_i_boxed_369_, v_stop_boxed_370_);
lean_dec_ref(v_as_366_);
lean_dec(v_a_365_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object* v_as_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_array_get_size(v_as_373_);
v___x_377_ = lean_nat_dec_lt(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
return v___x_377_;
}
else
{
if (v___x_377_ == 0)
{
return v___x_377_;
}
else
{
size_t v___x_378_; size_t v___x_379_; uint8_t v___x_380_; 
v___x_378_ = ((size_t)0ULL);
v___x_379_ = lean_usize_of_nat(v___x_376_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_374_, v_as_373_, v___x_378_, v___x_379_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_MVarId_rewrite_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_373_ = stack[0].m_obj;
lean_object* v_a_374_ = stack[1].m_obj;
uint8_t v_res_381_;
v_res_381_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_373_, v_a_374_);
stack->m_num = v_res_381_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* v_as_382_, lean_object* v_a_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_as_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object* v_a_386_, lean_object* v_as_387_, size_t v_i_388_, size_t v_stop_389_, lean_object* v_b_390_){
_start:
{
lean_object* v___y_392_; uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_eq(v_i_388_, v_stop_389_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_array_uget_borrowed(v_as_387_, v_i_388_);
v___x_398_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_a_386_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_inc(v___x_397_);
v___x_399_ = lean_array_push(v_b_390_, v___x_397_);
v___y_392_ = v___x_399_;
goto v___jp_391_;
}
else
{
v___y_392_ = v_b_390_;
goto v___jp_391_;
}
}
else
{
return v_b_390_;
}
v___jp_391_:
{
size_t v___x_393_; size_t v___x_394_; 
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_add(v_i_388_, v___x_393_);
v_i_388_ = v___x_394_;
v_b_390_ = v___y_392_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_386_ = stack[0].m_obj;
lean_object* v_as_387_ = stack[1].m_obj;
size_t v_i_388_ = stack[2].m_num;
size_t v_stop_389_ = stack[3].m_num;
lean_object* v_b_390_ = stack[4].m_obj;
lean_object* v_res_400_;
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_386_, v_as_387_, v_i_388_, v_stop_389_, v_b_390_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* v_a_401_, lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_, lean_object* v_b_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_stop_boxed_407_; lean_object* v_res_408_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_407_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_401_, v_as_402_, v_i_boxed_406_, v_stop_boxed_407_, v_b_405_);
lean_dec_ref(v_as_402_);
lean_dec_ref(v_a_401_);
return v_res_408_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(lean_object* v_msgData_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_env_416_; uint8_t v___x_417_; lean_object* v_env_418_; lean_object* v___x_419_; lean_object* v_toCold_420_; lean_object* v_mctx_421_; lean_object* v_lctx_422_; lean_object* v_options_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_415_ = lean_st_ref_get(v___y_413_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_env_416_);
lean_dec(v___x_415_);
v___x_417_ = 0;
v_env_418_ = l_Lean_Environment_setRecordingDeps(v_env_416_, v___x_417_);
v___x_419_ = lean_st_ref_get(v___y_411_);
v_toCold_420_ = lean_ctor_get(v___y_412_, 0);
v_mctx_421_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_mctx_421_);
lean_dec(v___x_419_);
v_lctx_422_ = lean_ctor_get(v___y_410_, 2);
v_options_423_ = lean_ctor_get(v_toCold_420_, 2);
lean_inc_ref(v_options_423_);
lean_inc_ref(v_lctx_422_);
v___x_424_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_424_, 0, v_env_418_);
lean_ctor_set(v___x_424_, 1, v_mctx_421_);
lean_ctor_set(v___x_424_, 2, v_lctx_422_);
lean_ctor_set(v___x_424_, 3, v_options_423_);
v___x_425_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_msgData_409_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_409_ = stack[0].m_obj;
lean_object* v___y_410_ = stack[1].m_obj;
lean_object* v___y_411_ = stack[2].m_obj;
lean_object* v___y_412_ = stack[3].m_obj;
lean_object* v___y_413_ = stack[4].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(lean_object* v_msgData_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_434_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_ref_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_451_; 
v_ref_441_ = lean_ctor_get(v___y_438_, 2);
v___x_442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_451_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
lean_inc(v_ref_441_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_ref_441_);
lean_ctor_set(v___x_447_, 1, v_a_443_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
lean_ctor_set(v___x_445_, 0, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_435_ = stack[0].m_obj;
lean_object* v___y_436_ = stack[1].m_obj;
lean_object* v___y_437_ = stack[2].m_obj;
lean_object* v___y_438_ = stack[3].m_obj;
lean_object* v___y_439_ = stack[4].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__0));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__2));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__7));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__9));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__11));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__13));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__15));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__17));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__19));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__24));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__28));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__32));
v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__34));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__36));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__38));
v___x_520_ = l_Lean_stringToMessageData(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__46(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_box(0);
v___x_530_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__45));
v___x_531_ = l_Lean_mkConst(v___x_530_, v___x_529_);
return v___x_531_;
}
}
lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* v_mvarId_532_, lean_object* v___x_533_, lean_object* v_heq_534_, lean_object* v_e_535_, lean_object* v_config_536_, uint8_t v_symm_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___x_571_; 
lean_inc(v___x_533_);
lean_inc(v_mvarId_532_);
v___x_571_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_532_, v___x_533_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; 
lean_dec_ref_known(v___x_571_, 1);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc_ref(v_heq_534_);
v___x_572_ = lean_infer_type(v_heq_534_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_1108_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_a_573_, v___y_539_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_1108_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_1108_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_box(0);
v___x_580_ = 0;
v___x_581_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_575_, v___x_579_, v___x_580_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v_snd_583_; lean_object* v_fst_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_1099_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v_snd_583_ = lean_ctor_get(v_a_582_, 1);
v_fst_584_ = lean_ctor_get(v_a_582_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_582_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_586_ = v_a_582_;
v_isShared_587_ = v_isSharedCheck_1099_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_583_);
lean_inc(v_fst_584_);
lean_dec(v_a_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_1099_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_1098_; 
v_fst_588_ = lean_ctor_get(v_snd_583_, 0);
v_snd_589_ = lean_ctor_get(v_snd_583_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_snd_583_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_591_ = v_snd_583_;
v_isShared_592_ = v_isSharedCheck_1098_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snd_589_);
lean_inc(v_fst_588_);
lean_dec(v_snd_583_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_1098_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___y_594_; size_t v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v_a_602_; lean_object* v___y_631_; lean_object* v___y_632_; size_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; uint8_t v___y_656_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v_eNew_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_994_; lean_object* v_heq_995_; lean_object* v_heqType_996_; lean_object* v_lhs_997_; lean_object* v_rhs_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v_heq_1022_; lean_object* v_heqType_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
lean_inc_ref(v_heq_534_);
v___x_1079_ = l_Lean_mkAppN(v_heq_534_, v_fst_584_);
v___x_1080_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__43));
v___x_1081_ = lean_unsigned_to_nat(2u);
v___x_1082_ = l_Lean_Expr_isAppOfArity(v_snd_589_, v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
v_heq_1022_ = v___x_1079_;
v_heqType_1023_ = v_snd_589_;
v___y_1024_ = v___y_538_;
v___y_1025_ = v___y_539_;
v___y_1026_ = v___y_540_;
v___y_1027_ = v___y_541_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = l_Lean_Expr_appFn_x21(v_snd_589_);
v___x_1084_ = l_Lean_Expr_appArg_x21(v___x_1083_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = l_Lean_Expr_appArg_x21(v_snd_589_);
lean_dec(v_snd_589_);
lean_inc_ref(v___x_1085_);
lean_inc_ref(v___x_1084_);
v___x_1086_ = l_Lean_Meta_mkEq(v___x_1084_, v___x_1085_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__46, &l_Lean_MVarId_rewrite___lam__1___closed__46_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__46);
v___x_1089_ = l_Lean_mkApp3(v___x_1088_, v___x_1084_, v___x_1085_, v___x_1079_);
v_heq_1022_ = v___x_1089_;
v_heqType_1023_ = v_a_1087_;
v___y_1024_ = v___y_538_;
v___y_1025_ = v___y_539_;
v___y_1026_ = v___y_540_;
v___y_1027_ = v___y_541_;
goto v___jp_1021_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_dec_ref(v___x_1079_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1090_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1086_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1086_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
v___jp_593_:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_appendParentTag(v_mvarId_532_, v_fst_584_, v_fst_588_, v___y_596_, v___y_598_, v___y_601_, v___y_599_);
lean_dec(v_fst_588_);
lean_dec(v_fst_584_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; 
lean_dec_ref_known(v___x_603_, 1);
v___x_604_ = l_Lean_Meta_getMVarsNoDelayed(v_heq_534_, v___y_596_, v___y_598_, v___y_601_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_596_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_array_get_size(v_a_605_);
v___x_607_ = lean_mk_empty_array_with_capacity(v___y_600_);
v___x_608_ = lean_nat_dec_lt(v___y_600_, v___x_606_);
if (v___x_608_ == 0)
{
lean_dec(v_a_605_);
v___y_563_ = v___y_594_;
v___y_564_ = v___y_597_;
v___y_565_ = v_a_602_;
v___y_566_ = v___x_607_;
goto v___jp_562_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_le(v___x_606_, v___x_606_);
if (v___x_609_ == 0)
{
if (v___x_608_ == 0)
{
lean_dec(v_a_605_);
v___y_563_ = v___y_594_;
v___y_564_ = v___y_597_;
v___y_565_ = v_a_602_;
v___y_566_ = v___x_607_;
goto v___jp_562_;
}
else
{
size_t v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_usize_of_nat(v___x_606_);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_602_, v_a_605_, v___y_595_, v___x_610_, v___x_607_);
lean_dec(v_a_605_);
v___y_563_ = v___y_594_;
v___y_564_ = v___y_597_;
v___y_565_ = v_a_602_;
v___y_566_ = v___x_611_;
goto v___jp_562_;
}
}
else
{
size_t v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_usize_of_nat(v___x_606_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_602_, v_a_605_, v___y_595_, v___x_612_, v___x_607_);
lean_dec(v_a_605_);
v___y_563_ = v___y_594_;
v___y_564_ = v___y_597_;
v___y_565_ = v_a_602_;
v___y_566_ = v___x_613_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_a_602_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_594_);
v_a_614_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_604_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_a_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_594_);
lean_dec_ref(v_heq_534_);
v_a_622_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_603_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_603_);
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
if (lean_obj_tag(v___y_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___y_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___y_639_, 1);
v___y_594_ = v___y_631_;
v___y_595_ = v___y_633_;
v___y_596_ = v___y_632_;
v___y_597_ = v___y_634_;
v___y_598_ = v___y_635_;
v___y_599_ = v___y_636_;
v___y_600_ = v___y_637_;
v___y_601_ = v___y_638_;
v_a_602_ = v_a_640_;
goto v___jp_593_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v___y_638_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v_fst_588_);
lean_dec(v_fst_584_);
lean_dec_ref(v_heq_534_);
lean_dec(v_mvarId_532_);
v_a_641_ = lean_ctor_get(v___y_639_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___y_639_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___y_639_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___y_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
v___jp_649_:
{
uint8_t v___x_657_; lean_object* v___x_658_; 
v___x_657_ = 0;
lean_inc(v_fst_588_);
lean_inc(v_mvarId_532_);
v___x_658_ = l_Lean_Meta_postprocessAppMVars(v___x_533_, v_mvarId_532_, v_fst_584_, v_fst_588_, v___y_656_, v___x_657_, v___y_651_, v___y_653_, v___y_655_, v___y_654_);
if (lean_obj_tag(v___x_658_) == 0)
{
size_t v_sz_659_; size_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
lean_dec_ref_known(v___x_658_, 1);
v_sz_659_ = lean_array_size(v_fst_584_);
v___x_660_ = ((size_t)0ULL);
lean_inc(v_fst_584_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_659_, v___x_660_, v_fst_584_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_array_get_size(v___x_661_);
v___x_664_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__4));
v___x_665_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
if (v___x_665_ == 0)
{
lean_dec_ref(v___x_661_);
v___y_594_ = v___y_650_;
v___y_595_ = v___x_660_;
v___y_596_ = v___y_651_;
v___y_597_ = v___y_652_;
v___y_598_ = v___y_653_;
v___y_599_ = v___y_654_;
v___y_600_ = v___x_662_;
v___y_601_ = v___y_655_;
v_a_602_ = v___x_664_;
goto v___jp_593_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_le(v___x_663_, v___x_663_);
if (v___x_666_ == 0)
{
if (v___x_665_ == 0)
{
lean_dec_ref(v___x_661_);
v___y_594_ = v___y_650_;
v___y_595_ = v___x_660_;
v___y_596_ = v___y_651_;
v___y_597_ = v___y_652_;
v___y_598_ = v___y_653_;
v___y_599_ = v___y_654_;
v___y_600_ = v___x_662_;
v___y_601_ = v___y_655_;
v_a_602_ = v___x_664_;
goto v___jp_593_;
}
else
{
size_t v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_usize_of_nat(v___x_663_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_661_, v___x_660_, v___x_667_, v___x_664_, v___y_651_, v___y_653_, v___y_655_, v___y_654_);
lean_dec_ref(v___x_661_);
v___y_631_ = v___y_650_;
v___y_632_ = v___y_651_;
v___y_633_ = v___x_660_;
v___y_634_ = v___y_652_;
v___y_635_ = v___y_653_;
v___y_636_ = v___y_654_;
v___y_637_ = v___x_662_;
v___y_638_ = v___y_655_;
v___y_639_ = v___x_668_;
goto v___jp_630_;
}
}
else
{
size_t v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_usize_of_nat(v___x_663_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_661_, v___x_660_, v___x_669_, v___x_664_, v___y_651_, v___y_653_, v___y_655_, v___y_654_);
lean_dec_ref(v___x_661_);
v___y_631_ = v___y_650_;
v___y_632_ = v___y_651_;
v___y_633_ = v___x_660_;
v___y_634_ = v___y_652_;
v___y_635_ = v___y_653_;
v___y_636_ = v___y_654_;
v___y_637_ = v___x_662_;
v___y_638_ = v___y_655_;
v___y_639_ = v___x_670_;
goto v___jp_630_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v_fst_588_);
lean_dec(v_fst_584_);
lean_dec_ref(v_heq_534_);
lean_dec(v_mvarId_532_);
v_a_671_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_658_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_658_);
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
v___jp_679_:
{
lean_object* v___x_691_; 
lean_inc_ref(v___y_686_);
v___x_691_ = l_Lean_Meta_getLevel(v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
lean_inc_ref(v___y_683_);
v___x_693_ = l_Lean_Meta_getLevel(v___y_683_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_696_ = lean_box(0);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 1);
lean_ctor_set(v___x_591_, 1, v___x_696_);
lean_ctor_set(v___x_591_, 0, v_a_694_);
v___x_698_ = v___x_591_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_694_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_709_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 1);
lean_ctor_set(v___x_586_, 1, v___x_698_);
lean_ctor_set(v___x_586_, 0, v_a_692_);
v___x_700_ = v___x_586_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_692_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_708_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_701_ = l_Lean_Expr_const___override(v___x_695_, v___x_700_);
v___x_702_ = l_Lean_mkApp6(v___x_701_, v___y_686_, v___y_683_, v___y_682_, v___y_685_, v___y_684_, v___y_681_);
v___x_703_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_689_);
v___x_704_ = l_Lean_Meta_tactic_skipAssignedInstances;
v___x_705_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v___x_703_, v___x_704_);
lean_dec_ref(v___x_703_);
if (v___x_705_ == 0)
{
uint8_t v___x_706_; 
v___x_706_ = 1;
v___y_650_ = v___y_680_;
v___y_651_ = v___y_687_;
v___y_652_ = v___x_702_;
v___y_653_ = v___y_688_;
v___y_654_ = v___y_690_;
v___y_655_ = v___y_689_;
v___y_656_ = v___x_706_;
goto v___jp_649_;
}
else
{
uint8_t v___x_707_; 
v___x_707_ = 0;
v___y_650_ = v___y_680_;
v___y_651_ = v___y_687_;
v___y_652_ = v___x_702_;
v___y_653_ = v___y_688_;
v___y_654_ = v___y_690_;
v___y_655_ = v___y_689_;
v___y_656_ = v___x_707_;
goto v___jp_649_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_a_692_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v___y_680_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_710_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_693_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_693_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v___y_680_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_718_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_691_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_691_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
v___jp_726_:
{
if (lean_obj_tag(v___y_741_) == 0)
{
lean_object* v___x_742_; 
lean_dec_ref_known(v___y_741_, 1);
lean_inc_ref(v___y_729_);
v___x_742_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v___y_732_, v___y_729_, v___y_733_, v___y_740_, v___y_735_, v___y_739_, v___y_728_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; uint8_t v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = lean_unbox(v_a_743_);
lean_dec(v_a_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_745_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__8, &l_Lean_MVarId_rewrite___lam__1___closed__8_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__8);
lean_inc_ref(v___y_737_);
v___x_746_ = l_Lean_MessageData_ofExpr(v___y_737_);
v___x_747_ = l_Lean_indentD(v___x_746_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_745_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__10, &l_Lean_MVarId_rewrite___lam__1___closed__10_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__10);
v___x_750_ = l_Lean_indentExpr(v___y_736_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__12, &l_Lean_MVarId_rewrite___lam__1___closed__12_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__12);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_inc_ref(v___y_734_);
v___x_754_ = l_Lean_indentExpr(v___y_734_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_MessageData_note(v___x_755_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_748_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 1);
lean_ctor_set(v___x_577_, 0, v___x_757_);
v___x_759_ = v___x_577_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_769_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
lean_inc(v_mvarId_532_);
lean_inc(v___x_533_);
v___x_760_ = l_Lean_Meta_throwTacticEx___redArg(v___x_533_, v_mvarId_532_, v___x_759_, v___y_740_, v___y_735_, v___y_739_, v___y_728_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_dec_ref_known(v___x_760_, 1);
v___y_680_ = v___y_730_;
v___y_681_ = v___y_731_;
v___y_682_ = v___y_734_;
v___y_683_ = v___y_727_;
v___y_684_ = v___y_737_;
v___y_685_ = v___y_738_;
v___y_686_ = v___y_729_;
v___y_687_ = v___y_740_;
v___y_688_ = v___y_735_;
v___y_689_ = v___y_739_;
v___y_690_ = v___y_728_;
goto v___jp_679_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_736_);
lean_del_object(v___x_577_);
v___y_680_ = v___y_730_;
v___y_681_ = v___y_731_;
v___y_682_ = v___y_734_;
v___y_683_ = v___y_727_;
v___y_684_ = v___y_737_;
v___y_685_ = v___y_738_;
v___y_686_ = v___y_729_;
v___y_687_ = v___y_740_;
v___y_688_ = v___y_735_;
v___y_689_ = v___y_739_;
v___y_690_ = v___y_728_;
goto v___jp_679_;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_770_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_742_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_742_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_778_ = lean_ctor_get(v___y_741_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___y_741_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___y_741_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___y_741_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
v___jp_786_:
{
if (v___y_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v___y_789_);
v___x_804_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__14, &l_Lean_MVarId_rewrite___lam__1___closed__14_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__14);
lean_inc_ref(v___y_799_);
v___x_805_ = l_Lean_MessageData_ofExpr(v___y_799_);
v___x_806_ = l_Lean_indentD(v___x_805_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__16, &l_Lean_MVarId_rewrite___lam__1___closed__16_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__16);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_Exception_toMessageData(v___y_798_);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__18, &l_Lean_MVarId_rewrite___lam__1___closed__18_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__18);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_815_ = l_Lean_MessageData_ofConstName(v___x_814_, v___y_803_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__20, &l_Lean_MVarId_rewrite___lam__1___closed__20_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__20);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__23));
v___x_820_ = l_Lean_MessageData_ofConstName(v___x_819_, v___y_803_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_818_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__25, &l_Lean_MVarId_rewrite___lam__1___closed__25_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__25);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__27));
v___x_825_ = l_Lean_MessageData_ofConstName(v___x_824_, v___y_803_);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__29, &l_Lean_MVarId_rewrite___lam__1___closed__29_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__29);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_inc(v_mvarId_532_);
lean_inc(v___x_533_);
v___x_830_ = l_Lean_Meta_throwTacticEx___redArg(v___x_533_, v_mvarId_532_, v___x_829_, v___y_802_, v___y_796_, v___y_801_, v___y_788_);
v___y_727_ = v___y_787_;
v___y_728_ = v___y_788_;
v___y_729_ = v___y_790_;
v___y_730_ = v___y_791_;
v___y_731_ = v___y_792_;
v___y_732_ = v___y_794_;
v___y_733_ = v___y_795_;
v___y_734_ = v___y_793_;
v___y_735_ = v___y_796_;
v___y_736_ = v___y_797_;
v___y_737_ = v___y_799_;
v___y_738_ = v___y_800_;
v___y_739_ = v___y_801_;
v___y_740_ = v___y_802_;
v___y_741_ = v___x_830_;
goto v___jp_726_;
}
else
{
lean_dec_ref(v___y_798_);
v___y_727_ = v___y_787_;
v___y_728_ = v___y_788_;
v___y_729_ = v___y_790_;
v___y_730_ = v___y_791_;
v___y_731_ = v___y_792_;
v___y_732_ = v___y_794_;
v___y_733_ = v___y_795_;
v___y_734_ = v___y_793_;
v___y_735_ = v___y_796_;
v___y_736_ = v___y_797_;
v___y_737_ = v___y_799_;
v___y_738_ = v___y_800_;
v___y_739_ = v___y_801_;
v___y_740_ = v___y_802_;
v___y_741_ = v___y_789_;
goto v___jp_726_;
}
}
v___jp_831_:
{
lean_object* v___x_844_; 
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc_ref(v___y_836_);
v___x_844_ = lean_infer_type(v___y_836_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___f_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_n(v_a_845_, 2);
lean_dec_ref_known(v___x_844_, 1);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(v___f_846_, 0, v___y_832_);
lean_closure_set(v___f_846_, 1, v_a_845_);
v___x_847_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__31));
v___x_848_ = 0;
lean_inc_ref(v___y_838_);
v___x_849_ = l_Lean_mkLambda(v___x_847_, v___x_848_, v___y_838_, v___y_835_);
v___x_850_ = 0;
lean_inc_ref(v___x_849_);
v___x_851_ = l_Lean_Meta_check(v___x_849_, v___x_850_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_851_) == 0)
{
v___y_727_ = v_a_845_;
v___y_728_ = v___y_843_;
v___y_729_ = v___y_838_;
v___y_730_ = v_eNew_839_;
v___y_731_ = v___y_833_;
v___y_732_ = v___x_847_;
v___y_733_ = v___f_846_;
v___y_734_ = v___y_834_;
v___y_735_ = v___y_841_;
v___y_736_ = v___y_836_;
v___y_737_ = v___x_849_;
v___y_738_ = v___y_837_;
v___y_739_ = v___y_842_;
v___y_740_ = v___y_840_;
v___y_741_ = v___x_851_;
goto v___jp_726_;
}
else
{
lean_object* v_a_852_; uint8_t v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
v___x_853_ = l_Lean_Exception_isInterrupt(v_a_852_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; 
lean_inc(v_a_852_);
v___x_854_ = l_Lean_Exception_isRuntime(v_a_852_);
v___y_787_ = v_a_845_;
v___y_788_ = v___y_843_;
v___y_789_ = v___x_851_;
v___y_790_ = v___y_838_;
v___y_791_ = v_eNew_839_;
v___y_792_ = v___y_833_;
v___y_793_ = v___y_834_;
v___y_794_ = v___x_847_;
v___y_795_ = v___f_846_;
v___y_796_ = v___y_841_;
v___y_797_ = v___y_836_;
v___y_798_ = v_a_852_;
v___y_799_ = v___x_849_;
v___y_800_ = v___y_837_;
v___y_801_ = v___y_842_;
v___y_802_ = v___y_840_;
v___y_803_ = v___x_854_;
goto v___jp_786_;
}
else
{
v___y_787_ = v_a_845_;
v___y_788_ = v___y_843_;
v___y_789_ = v___x_851_;
v___y_790_ = v___y_838_;
v___y_791_ = v_eNew_839_;
v___y_792_ = v___y_833_;
v___y_793_ = v___y_834_;
v___y_794_ = v___x_847_;
v___y_795_ = v___f_846_;
v___y_796_ = v___y_841_;
v___y_797_ = v___y_836_;
v___y_798_ = v_a_852_;
v___y_799_ = v___x_849_;
v___y_800_ = v___y_837_;
v___y_801_ = v___y_842_;
v___y_802_ = v___y_840_;
v___y_803_ = v___x_853_;
goto v___jp_786_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_eNew_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_832_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_855_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_844_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_844_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
v___jp_863_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_a_876_; uint8_t v___x_877_; 
v___x_874_ = lean_expr_instantiate1(v___y_864_, v___y_868_);
v___x_875_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v___x_874_, v___y_871_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = l_Lean_Expr_hasBinderNameHint(v___y_868_);
if (v___x_877_ == 0)
{
lean_inc_ref(v___y_864_);
v___y_832_ = v___y_864_;
v___y_833_ = v___y_865_;
v___y_834_ = v___y_866_;
v___y_835_ = v___y_864_;
v___y_836_ = v___y_867_;
v___y_837_ = v___y_868_;
v___y_838_ = v___y_869_;
v_eNew_839_ = v_a_876_;
v___y_840_ = v___y_870_;
v___y_841_ = v___y_871_;
v___y_842_ = v___y_872_;
v___y_843_ = v___y_873_;
goto v___jp_831_;
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Expr_resolveBinderNameHint(v_a_876_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
lean_inc_ref(v___y_864_);
v___y_832_ = v___y_864_;
v___y_833_ = v___y_865_;
v___y_834_ = v___y_866_;
v___y_835_ = v___y_864_;
v___y_836_ = v___y_867_;
v___y_837_ = v___y_868_;
v___y_838_ = v___y_869_;
v_eNew_839_ = v_a_879_;
v___y_840_ = v___y_870_;
v___y_841_ = v___y_871_;
v___y_842_ = v___y_872_;
v___y_843_ = v___y_873_;
goto v___jp_831_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v___y_864_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_880_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_878_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
v___jp_888_:
{
lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_992_; 
v___x_897_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_535_, v___y_894_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_992_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_992_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_992_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
uint8_t v_transparency_902_; uint8_t v_offsetCnstrs_903_; lean_object* v_occs_904_; lean_object* v___x_905_; uint8_t v_foApprox_906_; uint8_t v_ctxApprox_907_; uint8_t v_quasiPatternApprox_908_; uint8_t v_constApprox_909_; uint8_t v_isDefEqStuckEx_910_; uint8_t v_unificationHints_911_; uint8_t v_proofIrrelevance_912_; uint8_t v_assignSyntheticOpaque_913_; uint8_t v_etaStruct_914_; uint8_t v_univApprox_915_; uint8_t v_iota_916_; uint8_t v_beta_917_; uint8_t v_proj_918_; uint8_t v_zeta_919_; uint8_t v_zetaDelta_920_; uint8_t v_zetaUnused_921_; uint8_t v_zetaHave_922_; uint8_t v_canUnfoldPredicateConfig_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_991_; 
v_transparency_902_ = lean_ctor_get_uint8(v_config_536_, sizeof(void*)*1);
v_offsetCnstrs_903_ = lean_ctor_get_uint8(v_config_536_, sizeof(void*)*1 + 1);
v_occs_904_ = lean_ctor_get(v_config_536_, 0);
lean_inc(v_occs_904_);
lean_dec_ref(v_config_536_);
v___x_905_ = l_Lean_Meta_Context_config(v___y_893_);
v_foApprox_906_ = lean_ctor_get_uint8(v___x_905_, 0);
v_ctxApprox_907_ = lean_ctor_get_uint8(v___x_905_, 1);
v_quasiPatternApprox_908_ = lean_ctor_get_uint8(v___x_905_, 2);
v_constApprox_909_ = lean_ctor_get_uint8(v___x_905_, 3);
v_isDefEqStuckEx_910_ = lean_ctor_get_uint8(v___x_905_, 4);
v_unificationHints_911_ = lean_ctor_get_uint8(v___x_905_, 5);
v_proofIrrelevance_912_ = lean_ctor_get_uint8(v___x_905_, 6);
v_assignSyntheticOpaque_913_ = lean_ctor_get_uint8(v___x_905_, 7);
v_etaStruct_914_ = lean_ctor_get_uint8(v___x_905_, 10);
v_univApprox_915_ = lean_ctor_get_uint8(v___x_905_, 11);
v_iota_916_ = lean_ctor_get_uint8(v___x_905_, 12);
v_beta_917_ = lean_ctor_get_uint8(v___x_905_, 13);
v_proj_918_ = lean_ctor_get_uint8(v___x_905_, 14);
v_zeta_919_ = lean_ctor_get_uint8(v___x_905_, 15);
v_zetaDelta_920_ = lean_ctor_get_uint8(v___x_905_, 16);
v_zetaUnused_921_ = lean_ctor_get_uint8(v___x_905_, 17);
v_zetaHave_922_ = lean_ctor_get_uint8(v___x_905_, 18);
v_canUnfoldPredicateConfig_923_ = lean_ctor_get_uint8(v___x_905_, 19);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_991_ == 0)
{
v___x_925_ = v___x_905_;
v_isShared_926_ = v_isSharedCheck_991_;
goto v_resetjp_924_;
}
else
{
lean_dec(v___x_905_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_991_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
uint8_t v_trackZetaDelta_927_; lean_object* v_zetaDeltaSet_928_; lean_object* v_lctx_929_; lean_object* v_localInstances_930_; lean_object* v_defEqCtx_x3f_931_; lean_object* v_synthPendingDepth_932_; lean_object* v_customCanUnfoldPredicate_x3f_933_; uint8_t v_univApprox_934_; uint8_t v_inTypeClassResolution_935_; uint8_t v_cacheInferType_936_; lean_object* v___x_938_; 
v_trackZetaDelta_927_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7);
v_zetaDeltaSet_928_ = lean_ctor_get(v___y_893_, 1);
v_lctx_929_ = lean_ctor_get(v___y_893_, 2);
v_localInstances_930_ = lean_ctor_get(v___y_893_, 3);
v_defEqCtx_x3f_931_ = lean_ctor_get(v___y_893_, 4);
v_synthPendingDepth_932_ = lean_ctor_get(v___y_893_, 5);
v_customCanUnfoldPredicate_x3f_933_ = lean_ctor_get(v___y_893_, 6);
v_univApprox_934_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_935_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7 + 2);
v_cacheInferType_936_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*7 + 3);
if (v_isShared_926_ == 0)
{
v___x_938_ = v___x_925_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 0, v_foApprox_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 1, v_ctxApprox_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 2, v_quasiPatternApprox_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 3, v_constApprox_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 4, v_isDefEqStuckEx_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 5, v_unificationHints_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 6, v_proofIrrelevance_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 7, v_assignSyntheticOpaque_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 10, v_etaStruct_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 11, v_univApprox_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 12, v_iota_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 13, v_beta_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 14, v_proj_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 15, v_zeta_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 16, v_zetaDelta_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 17, v_zetaUnused_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 18, v_zetaHave_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, 19, v_canUnfoldPredicateConfig_923_);
v___x_938_ = v_reuseFailAlloc_990_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
uint64_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_ctor_set_uint8(v___x_938_, 8, v_offsetCnstrs_903_);
lean_ctor_set_uint8(v___x_938_, 9, v_transparency_902_);
v___x_939_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set_uint64(v___x_940_, sizeof(void*)*1, v___x_939_);
lean_inc(v_customCanUnfoldPredicate_x3f_933_);
lean_inc(v_synthPendingDepth_932_);
lean_inc(v_defEqCtx_x3f_931_);
lean_inc_ref(v_localInstances_930_);
lean_inc_ref(v_lctx_929_);
lean_inc(v_zetaDeltaSet_928_);
v___x_941_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v_zetaDeltaSet_928_);
lean_ctor_set(v___x_941_, 2, v_lctx_929_);
lean_ctor_set(v___x_941_, 3, v_localInstances_930_);
lean_ctor_set(v___x_941_, 4, v_defEqCtx_x3f_931_);
lean_ctor_set(v___x_941_, 5, v_synthPendingDepth_932_);
lean_ctor_set(v___x_941_, 6, v_customCanUnfoldPredicate_x3f_933_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*7, v_trackZetaDelta_927_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*7 + 1, v_univApprox_934_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*7 + 2, v_inTypeClassResolution_935_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*7 + 3, v_cacheInferType_936_);
lean_inc_ref(v___y_890_);
lean_inc(v_a_898_);
v___x_942_ = l_Lean_Meta_kabstract(v_a_898_, v___y_890_, v_occs_904_, v___x_941_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; uint8_t v___x_944_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = l_Lean_Expr_hasLooseBVars(v_a_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_inc_ref(v___y_890_);
lean_inc(v_a_898_);
v___x_945_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_898_, v___y_890_, v___x_941_, v___y_894_, v___y_895_, v___y_896_);
lean_dec_ref_known(v___x_941_, 7);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v_fst_947_; lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_973_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v_fst_947_ = lean_ctor_get(v_a_946_, 0);
v_snd_948_ = lean_ctor_get(v_a_946_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_946_);
if (v_isSharedCheck_973_ == 0)
{
v___x_950_ = v_a_946_;
v_isShared_951_ = v_isSharedCheck_973_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_inc(v_fst_947_);
lean_dec(v_a_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_973_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_952_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__33, &l_Lean_MVarId_rewrite___lam__1___closed__33_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__33);
v___x_953_ = l_Lean_indentExpr(v_snd_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 7);
lean_ctor_set(v___x_950_, 1, v___x_953_);
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_972_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_956_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__35, &l_Lean_MVarId_rewrite___lam__1___closed__35_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__35);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_indentExpr(v_fst_947_);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 0, v___x_959_);
v___x_961_ = v___x_900_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_971_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
lean_inc(v_mvarId_532_);
lean_inc(v___x_533_);
v___x_962_ = l_Lean_Meta_throwTacticEx___redArg(v___x_533_, v_mvarId_532_, v___x_961_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref_known(v___x_962_, 1);
v___y_864_ = v_a_943_;
v___y_865_ = v___y_889_;
v___y_866_ = v___y_890_;
v___y_867_ = v_a_898_;
v___y_868_ = v___y_891_;
v___y_869_ = v___y_892_;
v___y_870_ = v___y_893_;
v___y_871_ = v___y_894_;
v___y_872_ = v___y_895_;
v___y_873_ = v___y_896_;
goto v___jp_863_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_a_943_);
lean_dec(v_a_898_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_889_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_a_943_);
lean_del_object(v___x_900_);
lean_dec(v_a_898_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_889_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_974_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_945_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_945_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_941_, 7);
lean_del_object(v___x_900_);
v___y_864_ = v_a_943_;
v___y_865_ = v___y_889_;
v___y_866_ = v___y_890_;
v___y_867_ = v_a_898_;
v___y_868_ = v___y_891_;
v___y_869_ = v___y_892_;
v___y_870_ = v___y_893_;
v___y_871_ = v___y_894_;
v___y_872_ = v___y_895_;
v___y_873_ = v___y_896_;
goto v___jp_863_;
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref_known(v___x_941_, 7);
lean_del_object(v___x_900_);
lean_dec(v_a_898_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_889_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_982_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_942_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_942_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
}
v___jp_993_:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = l_Lean_Expr_getAppFn(v_lhs_997_);
v___x_1004_ = l_Lean_Expr_isMVar(v___x_1003_);
lean_dec_ref(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v_heqType_996_);
v___y_889_ = v_heq_995_;
v___y_890_ = v_lhs_997_;
v___y_891_ = v_rhs_998_;
v___y_892_ = v___y_994_;
v___y_893_ = v___y_999_;
v___y_894_ = v___y_1000_;
v___y_895_ = v___y_1001_;
v___y_896_ = v___y_1002_;
goto v___jp_888_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_rhs_998_);
lean_dec_ref(v_heq_995_);
lean_dec_ref(v___y_994_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v___x_1005_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__37, &l_Lean_MVarId_rewrite___lam__1___closed__37_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__37);
v___x_1006_ = l_Lean_MessageData_ofExpr(v_lhs_997_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__39, &l_Lean_MVarId_rewrite___lam__1___closed__39_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__39);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_indentExpr(v_heqType_996_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_1011_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
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
v___jp_1021_:
{
lean_object* v___x_1028_; 
lean_inc_ref(v_heqType_1023_);
v___x_1028_ = l_Lean_Meta_matchEq_x3f(v_heqType_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
if (lean_obj_tag(v_a_1029_) == 0)
{
lean_object* v___x_1030_; 
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
lean_inc_ref(v_heqType_1023_);
v___x_1030_ = l_Lean_Meta_isProp(v_heqType_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; uint8_t v___x_1032_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = lean_unbox(v_a_1031_);
lean_dec(v_a_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__40));
v___y_544_ = v___y_1025_;
v___y_545_ = v_heqType_1023_;
v___y_546_ = v___y_1024_;
v___y_547_ = v_heq_1022_;
v___y_548_ = v___y_1027_;
v___y_549_ = v___y_1026_;
v___y_550_ = v___x_1033_;
goto v___jp_543_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__41));
v___y_544_ = v___y_1025_;
v___y_545_ = v_heqType_1023_;
v___y_546_ = v___y_1024_;
v___y_547_ = v_heq_1022_;
v___y_548_ = v___y_1027_;
v___y_549_ = v___y_1026_;
v___y_550_ = v___x_1034_;
goto v___jp_543_;
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_heqType_1023_);
lean_dec_ref(v_heq_1022_);
v_a_1035_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1030_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1030_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_val_1043_; lean_object* v_snd_1044_; 
v_val_1043_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_val_1043_);
lean_dec_ref_known(v_a_1029_, 1);
v_snd_1044_ = lean_ctor_get(v_val_1043_, 1);
lean_inc(v_snd_1044_);
if (v_symm_537_ == 0)
{
lean_object* v_fst_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; 
v_fst_1045_ = lean_ctor_get(v_val_1043_, 0);
lean_inc(v_fst_1045_);
lean_dec(v_val_1043_);
v_fst_1046_ = lean_ctor_get(v_snd_1044_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v_snd_1044_, 1);
lean_inc(v_snd_1047_);
lean_dec(v_snd_1044_);
v___y_994_ = v_fst_1045_;
v_heq_995_ = v_heq_1022_;
v_heqType_996_ = v_heqType_1023_;
v_lhs_997_ = v_fst_1046_;
v_rhs_998_ = v_snd_1047_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v___y_1025_;
v___y_1001_ = v___y_1026_;
v___y_1002_ = v___y_1027_;
goto v___jp_993_;
}
else
{
lean_object* v_fst_1048_; lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_heqType_1023_);
v_fst_1048_ = lean_ctor_get(v_val_1043_, 0);
lean_inc(v_fst_1048_);
lean_dec(v_val_1043_);
v_fst_1049_ = lean_ctor_get(v_snd_1044_, 0);
lean_inc(v_fst_1049_);
v_snd_1050_ = lean_ctor_get(v_snd_1044_, 1);
lean_inc(v_snd_1050_);
lean_dec(v_snd_1044_);
v___x_1051_ = l_Lean_Meta_mkEqSymm(v_heq_1022_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
lean_inc(v_fst_1049_);
lean_inc(v_snd_1050_);
v___x_1053_ = l_Lean_Meta_mkEq(v_snd_1050_, v_fst_1049_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___y_994_ = v_fst_1048_;
v_heq_995_ = v_a_1052_;
v_heqType_996_ = v_a_1054_;
v_lhs_997_ = v_snd_1050_;
v_rhs_998_ = v_fst_1049_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v___y_1025_;
v___y_1001_ = v___y_1026_;
v___y_1002_ = v___y_1027_;
goto v___jp_993_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1052_);
lean_dec(v_snd_1050_);
lean_dec(v_fst_1049_);
lean_dec(v_fst_1048_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1055_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1053_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_snd_1050_);
lean_dec(v_fst_1049_);
lean_dec(v_fst_1048_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1063_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1051_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1051_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_heqType_1023_);
lean_dec_ref(v_heq_1022_);
lean_del_object(v___x_591_);
lean_dec(v_fst_588_);
lean_del_object(v___x_586_);
lean_dec(v_fst_584_);
lean_del_object(v___x_577_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1071_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1028_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1028_);
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
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_del_object(v___x_577_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1100_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_581_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_581_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1109_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_572_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_572_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_config_536_);
lean_dec_ref(v_e_535_);
lean_dec_ref(v_heq_534_);
lean_dec(v___x_533_);
lean_dec(v_mvarId_532_);
v_a_1117_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_571_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_571_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
v___jp_543_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_551_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__1, &l_Lean_MVarId_rewrite___lam__1___closed__1_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__1);
v___x_552_ = lean_unsigned_to_nat(30u);
v___x_553_ = l_Lean_inlineExpr(v___y_547_, v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__3, &l_Lean_MVarId_rewrite___lam__1___closed__3_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__3);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
lean_inc_ref(v___y_550_);
v___x_557_ = l_Lean_stringToMessageData(v___y_550_);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_Lean_indentExpr(v___y_545_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_560_, v___y_546_, v___y_544_, v___y_549_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_546_);
return v___x_561_;
}
v___jp_562_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = l_Array_append___redArg(v___y_565_, v___y_566_);
lean_dec_ref(v___y_566_);
v___x_568_ = lean_array_to_list(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v___y_563_);
lean_ctor_set(v___x_569_, 1, v___y_564_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_rewrite___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_532_ = stack[0].m_obj;
lean_object* v___x_533_ = stack[1].m_obj;
lean_object* v_heq_534_ = stack[2].m_obj;
lean_object* v_e_535_ = stack[3].m_obj;
lean_object* v_config_536_ = stack[4].m_obj;
uint8_t v_symm_537_ = stack[5].m_num;
lean_object* v___y_538_ = stack[6].m_obj;
lean_object* v___y_539_ = stack[7].m_obj;
lean_object* v___y_540_ = stack[8].m_obj;
lean_object* v___y_541_ = stack[9].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_532_, v___x_533_, v_heq_534_, v_e_535_, v_config_536_, v_symm_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* v_mvarId_1126_, lean_object* v___x_1127_, lean_object* v_heq_1128_, lean_object* v_e_1129_, lean_object* v_config_1130_, lean_object* v_symm_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_symm_boxed_1137_; lean_object* v_res_1138_; 
v_symm_boxed_1137_ = lean_unbox(v_symm_1131_);
v_res_1138_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_1126_, v___x_1127_, v_heq_1128_, v_e_1129_, v_config_1130_, v_symm_boxed_1137_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v_res_1138_;
}
}
lean_object* l_Lean_MVarId_rewrite(lean_object* v_mvarId_1142_, lean_object* v_e_1143_, lean_object* v_heq_1144_, uint8_t v_symm_1145_, lean_object* v_config_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; 
v___x_1152_ = ((lean_object*)(l_Lean_MVarId_rewrite___closed__1));
v___x_1153_ = lean_box(v_symm_1145_);
lean_inc(v_mvarId_1142_);
v___f_1154_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1154_, 0, v_mvarId_1142_);
lean_closure_set(v___f_1154_, 1, v___x_1152_);
lean_closure_set(v___f_1154_, 2, v_heq_1144_);
lean_closure_set(v___f_1154_, 3, v_e_1143_);
lean_closure_set(v___f_1154_, 4, v_config_1146_);
lean_closure_set(v___f_1154_, 5, v___x_1153_);
v___x_1155_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_1142_, v___f_1154_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1155_;
}
}
LEAN_EXPORT void l_Lean_MVarId_rewrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1142_ = stack[0].m_obj;
lean_object* v_e_1143_ = stack[1].m_obj;
lean_object* v_heq_1144_ = stack[2].m_obj;
uint8_t v_symm_1145_ = stack[3].m_num;
lean_object* v_config_1146_ = stack[4].m_obj;
lean_object* v_a_1147_ = stack[5].m_obj;
lean_object* v_a_1148_ = stack[6].m_obj;
lean_object* v_a_1149_ = stack[7].m_obj;
lean_object* v_a_1150_ = stack[8].m_obj;
lean_object* v_res_1156_;
v_res_1156_ = l_Lean_MVarId_rewrite(v_mvarId_1142_, v_e_1143_, v_heq_1144_, v_symm_1145_, v_config_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
stack->m_obj
 = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* v_mvarId_1157_, lean_object* v_e_1158_, lean_object* v_heq_1159_, lean_object* v_symm_1160_, lean_object* v_config_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
uint8_t v_symm_boxed_1167_; lean_object* v_res_1168_; 
v_symm_boxed_1167_ = lean_unbox(v_symm_1160_);
v_res_1168_ = l_Lean_MVarId_rewrite(v_mvarId_1157_, v_e_1158_, v_heq_1159_, v_symm_boxed_1167_, v_config_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1168_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* v_mvarId_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_1169_, v___y_1171_);
return v___x_1175_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1169_ = stack[0].m_obj;
lean_object* v___y_1170_ = stack[1].m_obj;
lean_object* v___y_1171_ = stack[2].m_obj;
lean_object* v___y_1172_ = stack[3].m_obj;
lean_object* v___y_1173_ = stack[4].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* v_mvarId_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v_mvarId_1177_);
return v_res_1183_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object* v_00_u03b1_1184_, lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1185_ = stack[1].m_obj;
lean_object* v___y_1186_ = stack[2].m_obj;
lean_object* v___y_1187_ = stack[3].m_obj;
lean_object* v___y_1188_ = stack[4].m_obj;
lean_object* v___y_1189_ = stack[5].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_box(0), v_msg_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object* v_00_u03b1_1193_, lean_object* v_msg_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(v_00_u03b1_1193_, v_msg_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_object* v_00_u03b1_1201_, lean_object* v_name_1202_, uint8_t v_bi_1203_, lean_object* v_type_1204_, lean_object* v_k_1205_, uint8_t v_kind_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1202_, v_bi_1203_, v_type_1204_, v_k_1205_, v_kind_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1202_ = stack[1].m_obj;
uint8_t v_bi_1203_ = stack[2].m_num;
lean_object* v_type_1204_ = stack[3].m_obj;
lean_object* v_k_1205_ = stack[4].m_obj;
uint8_t v_kind_1206_ = stack[5].m_num;
lean_object* v___y_1207_ = stack[6].m_obj;
lean_object* v___y_1208_ = stack[7].m_obj;
lean_object* v___y_1209_ = stack[8].m_obj;
lean_object* v___y_1210_ = stack[9].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_box(0), v_name_1202_, v_bi_1203_, v_type_1204_, v_k_1205_, v_kind_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_name_1215_, lean_object* v_bi_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, lean_object* v_kind_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_bi_boxed_1225_; uint8_t v_kind_boxed_1226_; lean_object* v_res_1227_; 
v_bi_boxed_1225_ = lean_unbox(v_bi_1216_);
v_kind_boxed_1226_ = lean_unbox(v_kind_1219_);
v_res_1227_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(v_00_u03b1_1214_, v_name_1215_, v_bi_boxed_1225_, v_type_1217_, v_k_1218_, v_kind_boxed_1226_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1227_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_object* v_00_u03b1_1228_, lean_object* v_name_1229_, lean_object* v_type_1230_, lean_object* v_k_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_1229_, v_type_1230_, v_k_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1229_ = stack[1].m_obj;
lean_object* v_type_1230_ = stack[2].m_obj;
lean_object* v_k_1231_ = stack[3].m_obj;
lean_object* v___y_1232_ = stack[4].m_obj;
lean_object* v___y_1233_ = stack[5].m_obj;
lean_object* v___y_1234_ = stack[6].m_obj;
lean_object* v___y_1235_ = stack[7].m_obj;
lean_object* v_res_1238_;
v_res_1238_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_box(0), v_name_1229_, v_type_1230_, v_k_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
stack->m_obj
 = v_res_1238_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_name_1240_, lean_object* v_type_1241_, lean_object* v_k_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(v_00_u03b1_1239_, v_name_1240_, v_type_1241_, v_k_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1248_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* v_00_u03b2_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1250_, v_x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1250_ = stack[1].m_obj;
lean_object* v_x_1251_ = stack[2].m_obj;
uint8_t v_res_1253_;
v_res_1253_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_box(0), v_x_1250_, v_x_1251_);
stack->m_num = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_1254_, v_x_1255_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec_ref(v_x_1255_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1259_, lean_object* v_x_1260_, size_t v_x_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1260_, v_x_1261_, v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1260_ = stack[1].m_obj;
size_t v_x_1261_ = stack[2].m_num;
lean_object* v_x_1262_ = stack[3].m_obj;
uint8_t v_res_1264_;
v_res_1264_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_box(0), v_x_1260_, v_x_1261_, v_x_1262_);
stack->m_num = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
size_t v_x_20885__boxed_1269_; uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_x_20885__boxed_1269_ = lean_unbox_usize(v_x_1267_);
lean_dec(v_x_1267_);
v_res_1270_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_1265_, v_x_1266_, v_x_20885__boxed_1269_, v_x_1268_);
lean_dec(v_x_1268_);
lean_dec_ref(v_x_1266_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_object* v_00_u03b2_1272_, lean_object* v_keys_1273_, lean_object* v_vals_1274_, lean_object* v_heq_1275_, lean_object* v_i_1276_, lean_object* v_k_1277_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_1273_, v_i_1276_, v_k_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1273_ = stack[1].m_obj;
lean_object* v_vals_1274_ = stack[2].m_obj;
lean_object* v_i_1276_ = stack[4].m_obj;
lean_object* v_k_1277_ = stack[5].m_obj;
uint8_t v_res_1279_;
v_res_1279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_box(0), v_keys_1273_, v_vals_1274_, lean_box(0), v_i_1276_, v_k_1277_);
stack->m_num = v_res_1279_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_keys_1281_, lean_object* v_vals_1282_, lean_object* v_heq_1283_, lean_object* v_i_1284_, lean_object* v_k_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(v_00_u03b2_1280_, v_keys_1281_, v_vals_1282_, v_heq_1283_, v_i_1284_, v_k_1285_);
lean_dec(v_k_1285_);
lean_dec_ref(v_vals_1282_);
lean_dec_ref(v_keys_1281_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
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
