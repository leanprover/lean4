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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1;
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
lean_dec_ref(v___x_49_);
if (lean_obj_tag(v_val_51_) == 1)
{
uint8_t v_v_52_; 
v_v_52_ = lean_ctor_get_uint8(v_val_51_, 0);
lean_dec_ref(v_val_51_);
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
lean_dec_ref(v___x_117_);
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
return v___x_161_;
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; 
v___x_170_ = ((size_t)5ULL);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_shift_left(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; 
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0);
v___x_175_ = lean_usize_sub(v___x_174_, v___x_173_);
return v___x_175_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(lean_object* v_x_176_, size_t v_x_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
lean_object* v_es_179_; lean_object* v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; lean_object* v_j_184_; lean_object* v___x_185_; 
v_es_179_ = lean_ctor_get(v_x_176_, 0);
v___x_180_ = lean_box(2);
v___x_181_ = ((size_t)5ULL);
v___x_182_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_183_ = lean_usize_land(v_x_177_, v___x_182_);
v_j_184_ = lean_usize_to_nat(v___x_183_);
v___x_185_ = lean_array_get_borrowed(v___x_180_, v_es_179_, v_j_184_);
lean_dec(v_j_184_);
switch(lean_obj_tag(v___x_185_))
{
case 0:
{
lean_object* v_key_186_; uint8_t v___x_187_; 
v_key_186_ = lean_ctor_get(v___x_185_, 0);
v___x_187_ = l_Lean_instBEqMVarId_beq(v_x_178_, v_key_186_);
return v___x_187_;
}
case 1:
{
lean_object* v_node_188_; size_t v___x_189_; 
v_node_188_ = lean_ctor_get(v___x_185_, 0);
v___x_189_ = lean_usize_shift_right(v_x_177_, v___x_181_);
v_x_176_ = v_node_188_;
v_x_177_ = v___x_189_;
goto _start;
}
default: 
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
}
}
else
{
lean_object* v_ks_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_ks_192_ = lean_ctor_get(v_x_176_, 0);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_ks_192_, v___x_193_, v_x_178_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
size_t v_x_18352__boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_x_18352__boxed_198_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_res_199_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_195_, v_x_18352__boxed_198_, v_x_197_);
lean_dec(v_x_197_);
lean_dec_ref(v_x_195_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint64_t v___x_203_; size_t v___x_204_; uint8_t v___x_205_; 
v___x_203_ = l_Lean_instHashableMVarId_hash(v_x_202_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_201_, v___x_204_, v_x_202_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_206_, v_x_207_);
lean_dec(v_x_207_);
lean_dec_ref(v_x_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(lean_object* v_mvarId_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_mctx_214_; lean_object* v_eAssignment_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_213_ = lean_st_ref_get(v___y_211_);
v_mctx_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_mctx_214_);
lean_dec(v___x_213_);
v_eAssignment_215_ = lean_ctor_get(v_mctx_214_, 8);
lean_inc_ref(v_eAssignment_215_);
lean_dec_ref(v_mctx_214_);
v___x_216_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_eAssignment_215_, v_mvarId_210_);
lean_dec_ref(v_eAssignment_215_);
v___x_217_ = lean_box(v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(lean_object* v_mvarId_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec(v_mvarId_219_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(lean_object* v_as_223_, size_t v_i_224_, size_t v_stop_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_a_233_; uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_eq(v_i_224_, v_stop_225_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_241_; 
v___x_238_ = lean_array_uget_borrowed(v_as_223_, v_i_224_);
v___x_241_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v___x_238_, v___y_228_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; uint8_t v___x_243_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref(v___x_241_);
v___x_243_ = lean_unbox(v_a_242_);
lean_dec(v_a_242_);
if (v___x_243_ == 0)
{
goto v___jp_239_;
}
else
{
v_a_233_ = v_b_226_;
goto v___jp_232_;
}
}
else
{
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_244_; uint8_t v___x_245_; 
v_a_244_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_244_);
lean_dec_ref(v___x_241_);
v___x_245_ = lean_unbox(v_a_244_);
lean_dec(v_a_244_);
if (v___x_245_ == 0)
{
v_a_233_ = v_b_226_;
goto v___jp_232_;
}
else
{
goto v___jp_239_;
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_b_226_);
v_a_246_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_241_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_241_);
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
v___jp_239_:
{
lean_object* v___x_240_; 
lean_inc(v___x_238_);
v___x_240_ = lean_array_push(v_b_226_, v___x_238_);
v_a_233_ = v___x_240_;
goto v___jp_232_;
}
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_b_226_);
return v___x_254_;
}
v___jp_232_:
{
size_t v___x_234_; size_t v___x_235_; 
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_224_, v___x_234_);
v_i_224_ = v___x_235_;
v_b_226_ = v_a_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
size_t v_i_boxed_264_; size_t v_stop_boxed_265_; lean_object* v_res_266_; 
v_i_boxed_264_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_265_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_255_, v_i_boxed_264_, v_stop_boxed_265_, v_b_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec_ref(v_as_255_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(lean_object* v_k_267_, lean_object* v_b_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
v___x_274_ = lean_apply_6(v_k_267_, v_b_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, lean_box(0));
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v_k_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_275_, v_b_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(lean_object* v_name_283_, uint8_t v_bi_284_, lean_object* v_type_285_, lean_object* v_k_286_, uint8_t v_kind_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___f_293_; lean_object* v___x_294_; 
v___f_293_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_293_, 0, v_k_286_);
v___x_294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_283_, v_bi_284_, v_type_285_, v___f_293_, v_kind_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_294_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_294_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(lean_object* v_name_311_, lean_object* v_bi_312_, lean_object* v_type_313_, lean_object* v_k_314_, lean_object* v_kind_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
uint8_t v_bi_boxed_321_; uint8_t v_kind_boxed_322_; lean_object* v_res_323_; 
v_bi_boxed_321_ = lean_unbox(v_bi_312_);
v_kind_boxed_322_ = lean_unbox(v_kind_315_);
v_res_323_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_311_, v_bi_boxed_321_, v_type_313_, v_k_314_, v_kind_boxed_322_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(lean_object* v_name_324_, lean_object* v_type_325_, lean_object* v_k_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = 0;
v___x_333_ = 0;
v___x_334_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_324_, v___x_332_, v_type_325_, v_k_326_, v___x_333_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(lean_object* v_name_335_, lean_object* v_type_336_, lean_object* v_k_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_335_, v_type_336_, v_k_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_343_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(lean_object* v_a_344_, lean_object* v_as_345_, size_t v_i_346_, size_t v_stop_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_eq(v_i_346_, v_stop_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_array_uget_borrowed(v_as_345_, v_i_346_);
v___x_350_ = l_Lean_instBEqMVarId_beq(v_a_344_, v___x_349_);
if (v___x_350_ == 0)
{
size_t v___x_351_; size_t v___x_352_; 
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_346_, v___x_351_);
v_i_346_ = v___x_352_;
goto _start;
}
else
{
return v___x_350_;
}
}
else
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6___boxed(lean_object* v_a_355_, lean_object* v_as_356_, lean_object* v_i_357_, lean_object* v_stop_358_){
_start:
{
size_t v_i_boxed_359_; size_t v_stop_boxed_360_; uint8_t v_res_361_; lean_object* v_r_362_; 
v_i_boxed_359_ = lean_unbox_usize(v_i_357_);
lean_dec(v_i_357_);
v_stop_boxed_360_ = lean_unbox_usize(v_stop_358_);
lean_dec(v_stop_358_);
v_res_361_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_355_, v_as_356_, v_i_boxed_359_, v_stop_boxed_360_);
lean_dec_ref(v_as_356_);
lean_dec(v_a_355_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(lean_object* v_as_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_array_get_size(v_as_363_);
v___x_367_ = lean_nat_dec_lt(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
return v___x_367_;
}
else
{
if (v___x_367_ == 0)
{
return v___x_367_;
}
else
{
size_t v___x_368_; size_t v___x_369_; uint8_t v___x_370_; 
v___x_368_ = ((size_t)0ULL);
v___x_369_ = lean_usize_of_nat(v___x_366_);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_364_, v_as_363_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(lean_object* v_as_371_, lean_object* v_a_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_as_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(lean_object* v_a_375_, lean_object* v_as_376_, size_t v_i_377_, size_t v_stop_378_, lean_object* v_b_379_){
_start:
{
lean_object* v___y_381_; uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_eq(v_i_377_, v_stop_378_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_array_uget_borrowed(v_as_376_, v_i_377_);
v___x_387_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_a_375_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_inc(v___x_386_);
v___x_388_ = lean_array_push(v_b_379_, v___x_386_);
v___y_381_ = v___x_388_;
goto v___jp_380_;
}
else
{
v___y_381_ = v_b_379_;
goto v___jp_380_;
}
}
else
{
return v_b_379_;
}
v___jp_380_:
{
size_t v___x_382_; size_t v___x_383_; 
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_377_, v___x_382_);
v_i_377_ = v___x_383_;
v_b_379_ = v___y_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(lean_object* v_a_389_, lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_, lean_object* v_b_393_){
_start:
{
size_t v_i_boxed_394_; size_t v_stop_boxed_395_; lean_object* v_res_396_; 
v_i_boxed_394_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_395_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_389_, v_as_390_, v_i_boxed_394_, v_stop_boxed_395_, v_b_393_);
lean_dec_ref(v_as_390_);
lean_dec_ref(v_a_389_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v_env_404_; lean_object* v___x_405_; lean_object* v_mctx_406_; lean_object* v_lctx_407_; lean_object* v_options_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_403_ = lean_st_ref_get(v___y_401_);
v_env_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_env_404_);
lean_dec(v___x_403_);
v___x_405_ = lean_st_ref_get(v___y_399_);
v_mctx_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_mctx_406_);
lean_dec(v___x_405_);
v_lctx_407_ = lean_ctor_get(v___y_398_, 2);
v_options_408_ = lean_ctor_get(v___y_400_, 2);
lean_inc_ref(v_options_408_);
lean_inc_ref(v_lctx_407_);
v___x_409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_409_, 0, v_env_404_);
lean_ctor_set(v___x_409_, 1, v_mctx_406_);
lean_ctor_set(v___x_409_, 2, v_lctx_407_);
lean_ctor_set(v___x_409_, 3, v_options_408_);
v___x_410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_msgData_397_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(lean_object* v_msgData_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_ref_425_; lean_object* v___x_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
v_ref_425_ = lean_ctor_get(v___y_422_, 5);
v___x_426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_435_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_inc(v_ref_425_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v_ref_425_);
lean_ctor_set(v___x_431_, 1, v_a_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 1);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__0));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__2));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__7));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__9));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__11));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__13));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__15));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__17));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__19));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__24));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__28));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__32));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__34));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__36));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__38));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__46(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_box(0);
v___x_513_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__45));
v___x_514_ = l_Lean_mkConst(v___x_513_, v___x_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* v_mvarId_515_, lean_object* v___x_516_, lean_object* v_heq_517_, lean_object* v_e_518_, lean_object* v_config_519_, uint8_t v_symm_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___x_554_; 
lean_inc(v___x_516_);
lean_inc(v_mvarId_515_);
v___x_554_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_515_, v___x_516_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v___x_554_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc_ref(v_heq_517_);
v___x_555_ = lean_infer_type(v_heq_517_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_1090_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v___x_555_);
v___x_557_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_a_556_, v___y_522_);
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_1090_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_1090_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
v___x_563_ = 0;
v___x_564_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_558_, v___x_562_, v___x_563_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v_snd_566_; lean_object* v_fst_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_1081_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref(v___x_564_);
v_snd_566_ = lean_ctor_get(v_a_565_, 1);
v_fst_567_ = lean_ctor_get(v_a_565_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_569_ = v_a_565_;
v_isShared_570_ = v_isSharedCheck_1081_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_567_);
lean_dec(v_a_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_1081_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_1080_; 
v_fst_571_ = lean_ctor_get(v_snd_566_, 0);
v_snd_572_ = lean_ctor_get(v_snd_566_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_snd_566_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_574_ = v_snd_566_;
v_isShared_575_ = v_isSharedCheck_1080_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_snd_572_);
lean_inc(v_fst_571_);
lean_dec(v_snd_566_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_1080_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___y_577_; size_t v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v_a_585_; lean_object* v___y_614_; lean_object* v___y_615_; size_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; uint8_t v___y_639_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v_eNew_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_976_; lean_object* v_heq_977_; lean_object* v_heqType_978_; lean_object* v_lhs_979_; lean_object* v_rhs_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v_heq_1004_; lean_object* v_heqType_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
lean_inc_ref(v_heq_517_);
v___x_1061_ = l_Lean_mkAppN(v_heq_517_, v_fst_567_);
v___x_1062_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__43));
v___x_1063_ = lean_unsigned_to_nat(2u);
v___x_1064_ = l_Lean_Expr_isAppOfArity(v_snd_572_, v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
v_heq_1004_ = v___x_1061_;
v_heqType_1005_ = v_snd_572_;
v___y_1006_ = v___y_521_;
v___y_1007_ = v___y_522_;
v___y_1008_ = v___y_523_;
v___y_1009_ = v___y_524_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1065_ = l_Lean_Expr_appFn_x21(v_snd_572_);
v___x_1066_ = l_Lean_Expr_appArg_x21(v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_Expr_appArg_x21(v_snd_572_);
lean_dec(v_snd_572_);
lean_inc_ref(v___x_1067_);
lean_inc_ref(v___x_1066_);
v___x_1068_ = l_Lean_Meta_mkEq(v___x_1066_, v___x_1067_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__46, &l_Lean_MVarId_rewrite___lam__1___closed__46_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__46);
v___x_1071_ = l_Lean_mkApp3(v___x_1070_, v___x_1066_, v___x_1067_, v___x_1061_);
v_heq_1004_ = v___x_1071_;
v_heqType_1005_ = v_a_1069_;
v___y_1006_ = v___y_521_;
v___y_1007_ = v___y_522_;
v___y_1008_ = v___y_523_;
v___y_1009_ = v___y_524_;
goto v___jp_1003_;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___x_1067_);
lean_dec_ref(v___x_1066_);
lean_dec_ref(v___x_1061_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1072_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1068_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
v___jp_576_:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_appendParentTag(v_mvarId_515_, v_fst_567_, v_fst_571_, v___y_583_, v___y_584_, v___y_582_, v___y_579_);
lean_dec(v_fst_571_);
lean_dec(v_fst_567_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v___x_586_);
v___x_587_ = l_Lean_Meta_getMVarsNoDelayed(v_heq_517_, v___y_583_, v___y_584_, v___y_582_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
v___x_589_ = lean_array_get_size(v_a_588_);
v___x_590_ = lean_mk_empty_array_with_capacity(v___y_577_);
v___x_591_ = lean_nat_dec_lt(v___y_577_, v___x_589_);
if (v___x_591_ == 0)
{
lean_dec(v_a_588_);
v___y_546_ = v___y_581_;
v___y_547_ = v___y_580_;
v___y_548_ = v_a_585_;
v___y_549_ = v___x_590_;
goto v___jp_545_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = lean_nat_dec_le(v___x_589_, v___x_589_);
if (v___x_592_ == 0)
{
if (v___x_591_ == 0)
{
lean_dec(v_a_588_);
v___y_546_ = v___y_581_;
v___y_547_ = v___y_580_;
v___y_548_ = v_a_585_;
v___y_549_ = v___x_590_;
goto v___jp_545_;
}
else
{
size_t v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_usize_of_nat(v___x_589_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_585_, v_a_588_, v___y_578_, v___x_593_, v___x_590_);
lean_dec(v_a_588_);
v___y_546_ = v___y_581_;
v___y_547_ = v___y_580_;
v___y_548_ = v_a_585_;
v___y_549_ = v___x_594_;
goto v___jp_545_;
}
}
else
{
size_t v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_usize_of_nat(v___x_589_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_585_, v_a_588_, v___y_578_, v___x_595_, v___x_590_);
lean_dec(v_a_588_);
v___y_546_ = v___y_581_;
v___y_547_ = v___y_580_;
v___y_548_ = v_a_585_;
v___y_549_ = v___x_596_;
goto v___jp_545_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_a_585_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v___y_580_);
v_a_597_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_587_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_a_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v_heq_517_);
v_a_605_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_586_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_586_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
v___jp_613_:
{
if (lean_obj_tag(v___y_622_) == 0)
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___y_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___y_622_);
v___y_577_ = v___y_614_;
v___y_578_ = v___y_616_;
v___y_579_ = v___y_615_;
v___y_580_ = v___y_618_;
v___y_581_ = v___y_617_;
v___y_582_ = v___y_619_;
v___y_583_ = v___y_620_;
v___y_584_ = v___y_621_;
v_a_585_ = v_a_623_;
goto v___jp_576_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_615_);
lean_dec(v_fst_571_);
lean_dec(v_fst_567_);
lean_dec_ref(v_heq_517_);
lean_dec(v_mvarId_515_);
v_a_624_ = lean_ctor_get(v___y_622_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___y_622_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___y_622_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___y_622_);
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
v___jp_632_:
{
uint8_t v___x_640_; lean_object* v___x_641_; 
v___x_640_ = 0;
lean_inc(v_fst_571_);
lean_inc(v_mvarId_515_);
v___x_641_ = l_Lean_Meta_postprocessAppMVars(v___x_516_, v_mvarId_515_, v_fst_567_, v_fst_571_, v___y_639_, v___x_640_, v___y_637_, v___y_638_, v___y_636_, v___y_633_);
if (lean_obj_tag(v___x_641_) == 0)
{
size_t v_sz_642_; size_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_dec_ref(v___x_641_);
v_sz_642_ = lean_array_size(v_fst_567_);
v___x_643_ = ((size_t)0ULL);
lean_inc(v_fst_567_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_642_, v___x_643_, v_fst_567_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_array_get_size(v___x_644_);
v___x_647_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__4));
v___x_648_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_648_ == 0)
{
lean_dec_ref(v___x_644_);
v___y_577_ = v___x_645_;
v___y_578_ = v___x_643_;
v___y_579_ = v___y_633_;
v___y_580_ = v___y_635_;
v___y_581_ = v___y_634_;
v___y_582_ = v___y_636_;
v___y_583_ = v___y_637_;
v___y_584_ = v___y_638_;
v_a_585_ = v___x_647_;
goto v___jp_576_;
}
else
{
uint8_t v___x_649_; 
v___x_649_ = lean_nat_dec_le(v___x_646_, v___x_646_);
if (v___x_649_ == 0)
{
if (v___x_648_ == 0)
{
lean_dec_ref(v___x_644_);
v___y_577_ = v___x_645_;
v___y_578_ = v___x_643_;
v___y_579_ = v___y_633_;
v___y_580_ = v___y_635_;
v___y_581_ = v___y_634_;
v___y_582_ = v___y_636_;
v___y_583_ = v___y_637_;
v___y_584_ = v___y_638_;
v_a_585_ = v___x_647_;
goto v___jp_576_;
}
else
{
size_t v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_usize_of_nat(v___x_646_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_644_, v___x_643_, v___x_650_, v___x_647_, v___y_637_, v___y_638_, v___y_636_, v___y_633_);
lean_dec_ref(v___x_644_);
v___y_614_ = v___x_645_;
v___y_615_ = v___y_633_;
v___y_616_ = v___x_643_;
v___y_617_ = v___y_634_;
v___y_618_ = v___y_635_;
v___y_619_ = v___y_636_;
v___y_620_ = v___y_637_;
v___y_621_ = v___y_638_;
v___y_622_ = v___x_651_;
goto v___jp_613_;
}
}
else
{
size_t v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_usize_of_nat(v___x_646_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_644_, v___x_643_, v___x_652_, v___x_647_, v___y_637_, v___y_638_, v___y_636_, v___y_633_);
lean_dec_ref(v___x_644_);
v___y_614_ = v___x_645_;
v___y_615_ = v___y_633_;
v___y_616_ = v___x_643_;
v___y_617_ = v___y_634_;
v___y_618_ = v___y_635_;
v___y_619_ = v___y_636_;
v___y_620_ = v___y_637_;
v___y_621_ = v___y_638_;
v___y_622_ = v___x_653_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec(v_fst_571_);
lean_dec(v_fst_567_);
lean_dec_ref(v_heq_517_);
lean_dec(v_mvarId_515_);
v_a_654_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_641_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_641_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
v___jp_662_:
{
lean_object* v___x_674_; 
lean_inc_ref(v___y_669_);
v___x_674_ = l_Lean_Meta_getLevel(v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref(v___x_674_);
lean_inc_ref(v___y_664_);
v___x_676_ = l_Lean_Meta_getLevel(v___y_664_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v_options_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
v_options_678_ = lean_ctor_get(v___y_672_, 2);
v___x_679_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_680_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 1, v___x_680_);
lean_ctor_set(v___x_574_, 0, v_a_677_);
v___x_682_ = v___x_574_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_692_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 1);
lean_ctor_set(v___x_569_, 1, v___x_682_);
lean_ctor_set(v___x_569_, 0, v_a_675_);
v___x_684_ = v___x_569_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_691_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_685_ = l_Lean_Expr_const___override(v___x_679_, v___x_684_);
v___x_686_ = l_Lean_mkApp6(v___x_685_, v___y_669_, v___y_664_, v___y_668_, v___y_665_, v___y_666_, v___y_667_);
v___x_687_ = l_Lean_Meta_tactic_skipAssignedInstances;
v___x_688_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v_options_678_, v___x_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; 
v___x_689_ = 1;
v___y_633_ = v___y_673_;
v___y_634_ = v___x_686_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_672_;
v___y_637_ = v___y_670_;
v___y_638_ = v___y_671_;
v___y_639_ = v___x_689_;
goto v___jp_632_;
}
else
{
uint8_t v___x_690_; 
v___x_690_ = 0;
v___y_633_ = v___y_673_;
v___y_634_ = v___x_686_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_672_;
v___y_637_ = v___y_670_;
v___y_638_ = v___y_671_;
v___y_639_ = v___x_690_;
goto v___jp_632_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v_a_675_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v___y_663_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_693_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_676_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_676_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v___y_663_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_701_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_674_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_674_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
v___jp_709_:
{
if (lean_obj_tag(v___y_724_) == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v___y_724_);
lean_inc_ref(v___y_722_);
v___x_725_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v___y_719_, v___y_722_, v___y_713_, v___y_715_, v___y_721_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; uint8_t v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_728_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__8, &l_Lean_MVarId_rewrite___lam__1___closed__8_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__8);
lean_inc_ref(v___y_720_);
v___x_729_ = l_Lean_MessageData_ofExpr(v___y_720_);
v___x_730_ = l_Lean_indentD(v___x_729_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_728_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__10, &l_Lean_MVarId_rewrite___lam__1___closed__10_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__10);
v___x_733_ = l_Lean_indentExpr(v___y_723_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__12, &l_Lean_MVarId_rewrite___lam__1___closed__12_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__12);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
lean_inc_ref(v___y_714_);
v___x_737_ = l_Lean_indentExpr(v___y_714_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_MessageData_note(v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_731_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 1);
lean_ctor_set(v___x_560_, 0, v___x_740_);
v___x_742_ = v___x_560_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_752_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
lean_inc(v_mvarId_515_);
lean_inc(v___x_516_);
v___x_743_ = l_Lean_Meta_throwTacticEx___redArg(v___x_516_, v_mvarId_515_, v___x_742_, v___y_715_, v___y_721_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref(v___x_743_);
v___y_663_ = v___y_710_;
v___y_664_ = v___y_716_;
v___y_665_ = v___y_711_;
v___y_666_ = v___y_720_;
v___y_667_ = v___y_712_;
v___y_668_ = v___y_714_;
v___y_669_ = v___y_722_;
v___y_670_ = v___y_715_;
v___y_671_ = v___y_721_;
v___y_672_ = v___y_717_;
v___y_673_ = v___y_718_;
goto v___jp_662_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_723_);
lean_del_object(v___x_560_);
v___y_663_ = v___y_710_;
v___y_664_ = v___y_716_;
v___y_665_ = v___y_711_;
v___y_666_ = v___y_720_;
v___y_667_ = v___y_712_;
v___y_668_ = v___y_714_;
v___y_669_ = v___y_722_;
v___y_670_ = v___y_715_;
v___y_671_ = v___y_721_;
v___y_672_ = v___y_717_;
v___y_673_ = v___y_718_;
goto v___jp_662_;
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_753_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_725_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_725_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_761_ = lean_ctor_get(v___y_724_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___y_724_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___y_724_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___y_724_);
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
v___jp_769_:
{
if (v___y_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec_ref(v___y_783_);
v___x_787_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__14, &l_Lean_MVarId_rewrite___lam__1___closed__14_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__14);
lean_inc_ref(v___y_781_);
v___x_788_ = l_Lean_MessageData_ofExpr(v___y_781_);
v___x_789_ = l_Lean_indentD(v___x_788_);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_787_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__16, &l_Lean_MVarId_rewrite___lam__1___closed__16_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__16);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_Exception_toMessageData(v___y_770_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__18, &l_Lean_MVarId_rewrite___lam__1___closed__18_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__18);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__6));
v___x_798_ = l_Lean_MessageData_ofConstName(v___x_797_, v___y_786_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__20, &l_Lean_MVarId_rewrite___lam__1___closed__20_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__20);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__23));
v___x_803_ = l_Lean_MessageData_ofConstName(v___x_802_, v___y_786_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_801_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__25, &l_Lean_MVarId_rewrite___lam__1___closed__25_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__25);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__27));
v___x_808_ = l_Lean_MessageData_ofConstName(v___x_807_, v___y_786_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__29, &l_Lean_MVarId_rewrite___lam__1___closed__29_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__29);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_inc(v_mvarId_515_);
lean_inc(v___x_516_);
v___x_813_ = l_Lean_Meta_throwTacticEx___redArg(v___x_516_, v_mvarId_515_, v___x_812_, v___y_776_, v___y_782_, v___y_778_, v___y_779_);
v___y_710_ = v___y_771_;
v___y_711_ = v___y_772_;
v___y_712_ = v___y_773_;
v___y_713_ = v___y_774_;
v___y_714_ = v___y_775_;
v___y_715_ = v___y_776_;
v___y_716_ = v___y_777_;
v___y_717_ = v___y_778_;
v___y_718_ = v___y_779_;
v___y_719_ = v___y_780_;
v___y_720_ = v___y_781_;
v___y_721_ = v___y_782_;
v___y_722_ = v___y_785_;
v___y_723_ = v___y_784_;
v___y_724_ = v___x_813_;
goto v___jp_709_;
}
else
{
lean_dec_ref(v___y_770_);
v___y_710_ = v___y_771_;
v___y_711_ = v___y_772_;
v___y_712_ = v___y_773_;
v___y_713_ = v___y_774_;
v___y_714_ = v___y_775_;
v___y_715_ = v___y_776_;
v___y_716_ = v___y_777_;
v___y_717_ = v___y_778_;
v___y_718_ = v___y_779_;
v___y_719_ = v___y_780_;
v___y_720_ = v___y_781_;
v___y_721_ = v___y_782_;
v___y_722_ = v___y_785_;
v___y_723_ = v___y_784_;
v___y_724_ = v___y_783_;
goto v___jp_709_;
}
}
v___jp_814_:
{
lean_object* v___x_827_; 
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc_ref(v___y_821_);
v___x_827_ = lean_infer_type(v___y_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___f_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_n(v_a_828_, 2);
lean_dec_ref(v___x_827_);
v___f_829_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(v___f_829_, 0, v___y_815_);
lean_closure_set(v___f_829_, 1, v_a_828_);
v___x_830_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__31));
v___x_831_ = 0;
lean_inc_ref(v___y_820_);
v___x_832_ = l_Lean_mkLambda(v___x_830_, v___x_831_, v___y_820_, v___y_816_);
v___x_833_ = 0;
lean_inc_ref(v___x_832_);
v___x_834_ = l_Lean_Meta_check(v___x_832_, v___x_833_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_834_) == 0)
{
v___y_710_ = v_eNew_822_;
v___y_711_ = v___y_817_;
v___y_712_ = v___y_818_;
v___y_713_ = v___f_829_;
v___y_714_ = v___y_819_;
v___y_715_ = v___y_823_;
v___y_716_ = v_a_828_;
v___y_717_ = v___y_825_;
v___y_718_ = v___y_826_;
v___y_719_ = v___x_830_;
v___y_720_ = v___x_832_;
v___y_721_ = v___y_824_;
v___y_722_ = v___y_820_;
v___y_723_ = v___y_821_;
v___y_724_ = v___x_834_;
goto v___jp_709_;
}
else
{
lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
v___x_836_ = l_Lean_Exception_isInterrupt(v_a_835_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; 
lean_inc(v_a_835_);
v___x_837_ = l_Lean_Exception_isRuntime(v_a_835_);
v___y_770_ = v_a_835_;
v___y_771_ = v_eNew_822_;
v___y_772_ = v___y_817_;
v___y_773_ = v___y_818_;
v___y_774_ = v___f_829_;
v___y_775_ = v___y_819_;
v___y_776_ = v___y_823_;
v___y_777_ = v_a_828_;
v___y_778_ = v___y_825_;
v___y_779_ = v___y_826_;
v___y_780_ = v___x_830_;
v___y_781_ = v___x_832_;
v___y_782_ = v___y_824_;
v___y_783_ = v___x_834_;
v___y_784_ = v___y_821_;
v___y_785_ = v___y_820_;
v___y_786_ = v___x_837_;
goto v___jp_769_;
}
else
{
v___y_770_ = v_a_835_;
v___y_771_ = v_eNew_822_;
v___y_772_ = v___y_817_;
v___y_773_ = v___y_818_;
v___y_774_ = v___f_829_;
v___y_775_ = v___y_819_;
v___y_776_ = v___y_823_;
v___y_777_ = v_a_828_;
v___y_778_ = v___y_825_;
v___y_779_ = v___y_826_;
v___y_780_ = v___x_830_;
v___y_781_ = v___x_832_;
v___y_782_ = v___y_824_;
v___y_783_ = v___x_834_;
v___y_784_ = v___y_821_;
v___y_785_ = v___y_820_;
v___y_786_ = v___x_836_;
goto v___jp_769_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v_eNew_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec_ref(v___y_815_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_838_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_827_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_827_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
v___jp_846_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_a_859_; uint8_t v___x_860_; 
v___x_857_ = lean_expr_instantiate1(v___y_847_, v___y_848_);
v___x_858_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v___x_857_, v___y_854_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = l_Lean_Expr_hasBinderNameHint(v___y_848_);
if (v___x_860_ == 0)
{
lean_inc_ref(v___y_847_);
v___y_815_ = v___y_847_;
v___y_816_ = v___y_847_;
v___y_817_ = v___y_848_;
v___y_818_ = v___y_849_;
v___y_819_ = v___y_850_;
v___y_820_ = v___y_852_;
v___y_821_ = v___y_851_;
v_eNew_822_ = v_a_859_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_854_;
v___y_825_ = v___y_855_;
v___y_826_ = v___y_856_;
goto v___jp_814_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Expr_resolveBinderNameHint(v_a_859_, v___y_855_, v___y_856_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
lean_inc_ref(v___y_847_);
v___y_815_ = v___y_847_;
v___y_816_ = v___y_847_;
v___y_817_ = v___y_848_;
v___y_818_ = v___y_849_;
v___y_819_ = v___y_850_;
v___y_820_ = v___y_852_;
v___y_821_ = v___y_851_;
v_eNew_822_ = v_a_862_;
v___y_823_ = v___y_853_;
v___y_824_ = v___y_854_;
v___y_825_ = v___y_855_;
v___y_826_ = v___y_856_;
goto v___jp_814_;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v___y_847_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_863_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_861_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
v___jp_871_:
{
lean_object* v___x_880_; lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_974_; 
v___x_880_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(v_e_518_, v___y_877_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_974_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_974_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_974_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v_transparency_885_; uint8_t v_offsetCnstrs_886_; lean_object* v_occs_887_; lean_object* v___x_888_; uint8_t v_foApprox_889_; uint8_t v_ctxApprox_890_; uint8_t v_quasiPatternApprox_891_; uint8_t v_constApprox_892_; uint8_t v_isDefEqStuckEx_893_; uint8_t v_unificationHints_894_; uint8_t v_proofIrrelevance_895_; uint8_t v_assignSyntheticOpaque_896_; uint8_t v_etaStruct_897_; uint8_t v_univApprox_898_; uint8_t v_iota_899_; uint8_t v_beta_900_; uint8_t v_proj_901_; uint8_t v_zeta_902_; uint8_t v_zetaDelta_903_; uint8_t v_zetaUnused_904_; uint8_t v_zetaHave_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_973_; 
v_transparency_885_ = lean_ctor_get_uint8(v_config_519_, sizeof(void*)*1);
v_offsetCnstrs_886_ = lean_ctor_get_uint8(v_config_519_, sizeof(void*)*1 + 1);
v_occs_887_ = lean_ctor_get(v_config_519_, 0);
lean_inc(v_occs_887_);
lean_dec_ref(v_config_519_);
v___x_888_ = l_Lean_Meta_Context_config(v___y_876_);
v_foApprox_889_ = lean_ctor_get_uint8(v___x_888_, 0);
v_ctxApprox_890_ = lean_ctor_get_uint8(v___x_888_, 1);
v_quasiPatternApprox_891_ = lean_ctor_get_uint8(v___x_888_, 2);
v_constApprox_892_ = lean_ctor_get_uint8(v___x_888_, 3);
v_isDefEqStuckEx_893_ = lean_ctor_get_uint8(v___x_888_, 4);
v_unificationHints_894_ = lean_ctor_get_uint8(v___x_888_, 5);
v_proofIrrelevance_895_ = lean_ctor_get_uint8(v___x_888_, 6);
v_assignSyntheticOpaque_896_ = lean_ctor_get_uint8(v___x_888_, 7);
v_etaStruct_897_ = lean_ctor_get_uint8(v___x_888_, 10);
v_univApprox_898_ = lean_ctor_get_uint8(v___x_888_, 11);
v_iota_899_ = lean_ctor_get_uint8(v___x_888_, 12);
v_beta_900_ = lean_ctor_get_uint8(v___x_888_, 13);
v_proj_901_ = lean_ctor_get_uint8(v___x_888_, 14);
v_zeta_902_ = lean_ctor_get_uint8(v___x_888_, 15);
v_zetaDelta_903_ = lean_ctor_get_uint8(v___x_888_, 16);
v_zetaUnused_904_ = lean_ctor_get_uint8(v___x_888_, 17);
v_zetaHave_905_ = lean_ctor_get_uint8(v___x_888_, 18);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_973_ == 0)
{
v___x_907_ = v___x_888_;
v_isShared_908_ = v_isSharedCheck_973_;
goto v_resetjp_906_;
}
else
{
lean_dec(v___x_888_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_973_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
uint8_t v_trackZetaDelta_909_; lean_object* v_zetaDeltaSet_910_; lean_object* v_lctx_911_; lean_object* v_localInstances_912_; lean_object* v_defEqCtx_x3f_913_; lean_object* v_synthPendingDepth_914_; lean_object* v_canUnfold_x3f_915_; uint8_t v_univApprox_916_; uint8_t v_inTypeClassResolution_917_; uint8_t v_cacheInferType_918_; lean_object* v___x_920_; 
v_trackZetaDelta_909_ = lean_ctor_get_uint8(v___y_876_, sizeof(void*)*7);
v_zetaDeltaSet_910_ = lean_ctor_get(v___y_876_, 1);
v_lctx_911_ = lean_ctor_get(v___y_876_, 2);
v_localInstances_912_ = lean_ctor_get(v___y_876_, 3);
v_defEqCtx_x3f_913_ = lean_ctor_get(v___y_876_, 4);
v_synthPendingDepth_914_ = lean_ctor_get(v___y_876_, 5);
v_canUnfold_x3f_915_ = lean_ctor_get(v___y_876_, 6);
v_univApprox_916_ = lean_ctor_get_uint8(v___y_876_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_917_ = lean_ctor_get_uint8(v___y_876_, sizeof(void*)*7 + 2);
v_cacheInferType_918_ = lean_ctor_get_uint8(v___y_876_, sizeof(void*)*7 + 3);
if (v_isShared_908_ == 0)
{
v___x_920_ = v___x_907_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 0, v_foApprox_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 1, v_ctxApprox_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 2, v_quasiPatternApprox_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 3, v_constApprox_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 4, v_isDefEqStuckEx_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 5, v_unificationHints_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 6, v_proofIrrelevance_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 7, v_assignSyntheticOpaque_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 10, v_etaStruct_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 11, v_univApprox_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 12, v_iota_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 13, v_beta_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 14, v_proj_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 15, v_zeta_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 16, v_zetaDelta_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 17, v_zetaUnused_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, 18, v_zetaHave_905_);
v___x_920_ = v_reuseFailAlloc_972_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
uint64_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_ctor_set_uint8(v___x_920_, 8, v_offsetCnstrs_886_);
lean_ctor_set_uint8(v___x_920_, 9, v_transparency_885_);
v___x_921_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set_uint64(v___x_922_, sizeof(void*)*1, v___x_921_);
lean_inc(v_canUnfold_x3f_915_);
lean_inc(v_synthPendingDepth_914_);
lean_inc(v_defEqCtx_x3f_913_);
lean_inc_ref(v_localInstances_912_);
lean_inc_ref(v_lctx_911_);
lean_inc(v_zetaDeltaSet_910_);
v___x_923_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_zetaDeltaSet_910_);
lean_ctor_set(v___x_923_, 2, v_lctx_911_);
lean_ctor_set(v___x_923_, 3, v_localInstances_912_);
lean_ctor_set(v___x_923_, 4, v_defEqCtx_x3f_913_);
lean_ctor_set(v___x_923_, 5, v_synthPendingDepth_914_);
lean_ctor_set(v___x_923_, 6, v_canUnfold_x3f_915_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7, v_trackZetaDelta_909_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7 + 1, v_univApprox_916_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7 + 2, v_inTypeClassResolution_917_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7 + 3, v_cacheInferType_918_);
lean_inc_ref(v___y_874_);
lean_inc(v_a_881_);
v___x_924_ = l_Lean_Meta_kabstract(v_a_881_, v___y_874_, v_occs_887_, v___x_923_, v___y_877_, v___y_878_, v___y_879_);
lean_dec_ref(v___x_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; uint8_t v___x_926_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_Expr_hasLooseBVars(v_a_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_inc_ref(v___y_874_);
lean_inc(v_a_881_);
v___x_927_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_881_, v___y_874_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_fst_929_; lean_object* v_snd_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_955_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref(v___x_927_);
v_fst_929_ = lean_ctor_get(v_a_928_, 0);
v_snd_930_ = lean_ctor_get(v_a_928_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_955_ == 0)
{
v___x_932_ = v_a_928_;
v_isShared_933_ = v_isSharedCheck_955_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_snd_930_);
lean_inc(v_fst_929_);
lean_dec(v_a_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_955_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__33, &l_Lean_MVarId_rewrite___lam__1___closed__33_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__33);
v___x_935_ = l_Lean_indentExpr(v_snd_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 7);
lean_ctor_set(v___x_932_, 1, v___x_935_);
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_935_);
v___x_937_ = v_reuseFailAlloc_954_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_938_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__35, &l_Lean_MVarId_rewrite___lam__1___closed__35_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__35);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_indentExpr(v_fst_929_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 1);
lean_ctor_set(v___x_883_, 0, v___x_941_);
v___x_943_ = v___x_883_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_953_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
lean_inc(v_mvarId_515_);
lean_inc(v___x_516_);
v___x_944_ = l_Lean_Meta_throwTacticEx___redArg(v___x_516_, v_mvarId_515_, v___x_943_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref(v___x_944_);
v___y_847_ = v_a_925_;
v___y_848_ = v___y_872_;
v___y_849_ = v___y_873_;
v___y_850_ = v___y_874_;
v___y_851_ = v_a_881_;
v___y_852_ = v___y_875_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_877_;
v___y_855_ = v___y_878_;
v___y_856_ = v___y_879_;
goto v___jp_846_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_925_);
lean_dec(v_a_881_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v___y_872_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
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
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_a_925_);
lean_del_object(v___x_883_);
lean_dec(v_a_881_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v___y_872_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_956_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_927_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_927_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_del_object(v___x_883_);
v___y_847_ = v_a_925_;
v___y_848_ = v___y_872_;
v___y_849_ = v___y_873_;
v___y_850_ = v___y_874_;
v___y_851_ = v_a_881_;
v___y_852_ = v___y_875_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_877_;
v___y_855_ = v___y_878_;
v___y_856_ = v___y_879_;
goto v___jp_846_;
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_del_object(v___x_883_);
lean_dec(v_a_881_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v___y_872_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_964_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_924_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_924_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
}
v___jp_975_:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = l_Lean_Expr_getAppFn(v_lhs_979_);
v___x_986_ = l_Lean_Expr_isMVar(v___x_985_);
lean_dec_ref(v___x_985_);
if (v___x_986_ == 0)
{
lean_dec_ref(v_heqType_978_);
v___y_872_ = v_rhs_980_;
v___y_873_ = v_heq_977_;
v___y_874_ = v_lhs_979_;
v___y_875_ = v___y_976_;
v___y_876_ = v___y_981_;
v___y_877_ = v___y_982_;
v___y_878_ = v___y_983_;
v___y_879_ = v___y_984_;
goto v___jp_871_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v_rhs_980_);
lean_dec_ref(v_heq_977_);
lean_dec_ref(v___y_976_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v___x_987_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__37, &l_Lean_MVarId_rewrite___lam__1___closed__37_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__37);
v___x_988_ = l_Lean_MessageData_ofExpr(v_lhs_979_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__39, &l_Lean_MVarId_rewrite___lam__1___closed__39_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__39);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_indentExpr(v_heqType_978_);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_993_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
v___jp_1003_:
{
lean_object* v___x_1010_; 
lean_inc_ref(v_heqType_1005_);
v___x_1010_ = l_Lean_Meta_matchEq_x3f(v_heqType_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
if (lean_obj_tag(v_a_1011_) == 0)
{
lean_object* v___x_1012_; 
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
lean_inc_ref(v_heqType_1005_);
v___x_1012_ = l_Lean_Meta_isProp(v_heqType_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; uint8_t v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_unbox(v_a_1013_);
lean_dec(v_a_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__40));
v___y_527_ = v___y_1008_;
v___y_528_ = v___y_1006_;
v___y_529_ = v_heqType_1005_;
v___y_530_ = v___y_1007_;
v___y_531_ = v_heq_1004_;
v___y_532_ = v___y_1009_;
v___y_533_ = v___x_1015_;
goto v___jp_526_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = ((lean_object*)(l_Lean_MVarId_rewrite___lam__1___closed__41));
v___y_527_ = v___y_1008_;
v___y_528_ = v___y_1006_;
v___y_529_ = v_heqType_1005_;
v___y_530_ = v___y_1007_;
v___y_531_ = v_heq_1004_;
v___y_532_ = v___y_1009_;
v___y_533_ = v___x_1016_;
goto v___jp_526_;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_heqType_1005_);
lean_dec_ref(v_heq_1004_);
v_a_1017_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1012_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1012_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_val_1025_; lean_object* v_snd_1026_; 
v_val_1025_ = lean_ctor_get(v_a_1011_, 0);
lean_inc(v_val_1025_);
lean_dec_ref(v_a_1011_);
v_snd_1026_ = lean_ctor_get(v_val_1025_, 1);
lean_inc(v_snd_1026_);
if (v_symm_520_ == 0)
{
lean_object* v_fst_1027_; lean_object* v_fst_1028_; lean_object* v_snd_1029_; 
v_fst_1027_ = lean_ctor_get(v_val_1025_, 0);
lean_inc(v_fst_1027_);
lean_dec(v_val_1025_);
v_fst_1028_ = lean_ctor_get(v_snd_1026_, 0);
lean_inc(v_fst_1028_);
v_snd_1029_ = lean_ctor_get(v_snd_1026_, 1);
lean_inc(v_snd_1029_);
lean_dec(v_snd_1026_);
v___y_976_ = v_fst_1027_;
v_heq_977_ = v_heq_1004_;
v_heqType_978_ = v_heqType_1005_;
v_lhs_979_ = v_fst_1028_;
v_rhs_980_ = v_snd_1029_;
v___y_981_ = v___y_1006_;
v___y_982_ = v___y_1007_;
v___y_983_ = v___y_1008_;
v___y_984_ = v___y_1009_;
goto v___jp_975_;
}
else
{
lean_object* v_fst_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_heqType_1005_);
v_fst_1030_ = lean_ctor_get(v_val_1025_, 0);
lean_inc(v_fst_1030_);
lean_dec(v_val_1025_);
v_fst_1031_ = lean_ctor_get(v_snd_1026_, 0);
lean_inc(v_fst_1031_);
v_snd_1032_ = lean_ctor_get(v_snd_1026_, 1);
lean_inc(v_snd_1032_);
lean_dec(v_snd_1026_);
v___x_1033_ = l_Lean_Meta_mkEqSymm(v_heq_1004_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref(v___x_1033_);
lean_inc(v_fst_1031_);
lean_inc(v_snd_1032_);
v___x_1035_ = l_Lean_Meta_mkEq(v_snd_1032_, v_fst_1031_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___y_976_ = v_fst_1030_;
v_heq_977_ = v_a_1034_;
v_heqType_978_ = v_a_1036_;
v_lhs_979_ = v_snd_1032_;
v_rhs_980_ = v_fst_1031_;
v___y_981_ = v___y_1006_;
v___y_982_ = v___y_1007_;
v___y_983_ = v___y_1008_;
v___y_984_ = v___y_1009_;
goto v___jp_975_;
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v_a_1034_);
lean_dec(v_snd_1032_);
lean_dec(v_fst_1031_);
lean_dec(v_fst_1030_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1037_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1035_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_snd_1032_);
lean_dec(v_fst_1031_);
lean_dec(v_fst_1030_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1045_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1033_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1033_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
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
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_heqType_1005_);
lean_dec_ref(v_heq_1004_);
lean_del_object(v___x_574_);
lean_dec(v_fst_571_);
lean_del_object(v___x_569_);
lean_dec(v_fst_567_);
lean_del_object(v___x_560_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1053_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1010_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1010_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_del_object(v___x_560_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1082_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_564_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_564_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
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
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1091_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_555_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_555_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_config_519_);
lean_dec_ref(v_e_518_);
lean_dec_ref(v_heq_517_);
lean_dec(v___x_516_);
lean_dec(v_mvarId_515_);
v_a_1099_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_554_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_554_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
v___jp_526_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_534_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__1, &l_Lean_MVarId_rewrite___lam__1___closed__1_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__1);
v___x_535_ = lean_unsigned_to_nat(30u);
v___x_536_ = l_Lean_inlineExpr(v___y_531_, v___x_535_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_534_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Lean_MVarId_rewrite___lam__1___closed__3, &l_Lean_MVarId_rewrite___lam__1___closed__3_once, _init_l_Lean_MVarId_rewrite___lam__1___closed__3);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_inc_ref(v___y_533_);
v___x_540_ = l_Lean_stringToMessageData(v___y_533_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_indentExpr(v___y_529_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v___x_543_, v___y_528_, v___y_530_, v___y_527_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_528_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = l_Array_append___redArg(v___y_548_, v___y_549_);
lean_dec_ref(v___y_549_);
v___x_551_ = lean_array_to_list(v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___y_547_);
lean_ctor_set(v___x_552_, 1, v___y_546_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* v_mvarId_1107_, lean_object* v___x_1108_, lean_object* v_heq_1109_, lean_object* v_e_1110_, lean_object* v_config_1111_, lean_object* v_symm_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_symm_boxed_1118_; lean_object* v_res_1119_; 
v_symm_boxed_1118_ = lean_unbox(v_symm_1112_);
v_res_1119_ = l_Lean_MVarId_rewrite___lam__1(v_mvarId_1107_, v___x_1108_, v_heq_1109_, v_e_1110_, v_config_1111_, v_symm_boxed_1118_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* v_mvarId_1123_, lean_object* v_e_1124_, lean_object* v_heq_1125_, uint8_t v_symm_1126_, lean_object* v_config_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v___x_1133_ = ((lean_object*)(l_Lean_MVarId_rewrite___closed__1));
v___x_1134_ = lean_box(v_symm_1126_);
lean_inc(v_mvarId_1123_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(v___f_1135_, 0, v_mvarId_1123_);
lean_closure_set(v___f_1135_, 1, v___x_1133_);
lean_closure_set(v___f_1135_, 2, v_heq_1125_);
lean_closure_set(v___f_1135_, 3, v_e_1124_);
lean_closure_set(v___f_1135_, 4, v_config_1127_);
lean_closure_set(v___f_1135_, 5, v___x_1134_);
v___x_1136_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(v_mvarId_1123_, v___f_1135_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* v_mvarId_1137_, lean_object* v_e_1138_, lean_object* v_heq_1139_, lean_object* v_symm_1140_, lean_object* v_config_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
uint8_t v_symm_boxed_1147_; lean_object* v_res_1148_; 
v_symm_boxed_1147_ = lean_unbox(v_symm_1140_);
v_res_1148_ = l_Lean_MVarId_rewrite(v_mvarId_1137_, v_e_1138_, v_heq_1139_, v_symm_boxed_1147_, v_config_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(lean_object* v_mvarId_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(v_mvarId_1149_, v___y_1151_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(lean_object* v_mvarId_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(v_mvarId_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v_mvarId_1156_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(lean_object* v_00_u03b1_1163_, lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(v_msg_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_msg_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(v_00_u03b1_1171_, v_msg_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(lean_object* v_00_u03b1_1179_, lean_object* v_name_1180_, uint8_t v_bi_1181_, lean_object* v_type_1182_, lean_object* v_k_1183_, uint8_t v_kind_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1180_, v_bi_1181_, v_type_1182_, v_k_1183_, v_kind_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_name_1192_, lean_object* v_bi_1193_, lean_object* v_type_1194_, lean_object* v_k_1195_, lean_object* v_kind_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v_bi_boxed_1202_; uint8_t v_kind_boxed_1203_; lean_object* v_res_1204_; 
v_bi_boxed_1202_ = lean_unbox(v_bi_1193_);
v_kind_boxed_1203_ = lean_unbox(v_kind_1196_);
v_res_1204_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(v_00_u03b1_1191_, v_name_1192_, v_bi_boxed_1202_, v_type_1194_, v_k_1195_, v_kind_boxed_1203_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(lean_object* v_00_u03b1_1205_, lean_object* v_name_1206_, lean_object* v_type_1207_, lean_object* v_k_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(v_name_1206_, v_type_1207_, v_k_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_name_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(v_00_u03b1_1215_, v_name_1216_, v_type_1217_, v_k_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1224_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1226_, v_x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_1229_, v_x_1230_, v_x_1231_);
lean_dec(v_x_1231_);
lean_dec_ref(v_x_1230_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1234_, lean_object* v_x_1235_, size_t v_x_1236_, lean_object* v_x_1237_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1235_, v_x_1236_, v_x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
size_t v_x_20113__boxed_1243_; uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_x_20113__boxed_1243_ = lean_unbox_usize(v_x_1241_);
lean_dec(v_x_1241_);
v_res_1244_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_1239_, v_x_1240_, v_x_20113__boxed_1243_, v_x_1242_);
lean_dec(v_x_1242_);
lean_dec_ref(v_x_1240_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(lean_object* v_00_u03b2_1246_, lean_object* v_keys_1247_, lean_object* v_vals_1248_, lean_object* v_heq_1249_, lean_object* v_i_1250_, lean_object* v_k_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_1247_, v_i_1250_, v_k_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_keys_1254_, lean_object* v_vals_1255_, lean_object* v_heq_1256_, lean_object* v_i_1257_, lean_object* v_k_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(v_00_u03b2_1253_, v_keys_1254_, v_vals_1255_, v_heq_1256_, v_i_1257_, v_k_1258_);
lean_dec(v_k_1258_);
lean_dec_ref(v_vals_1255_);
lean_dec_ref(v_keys_1254_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
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
