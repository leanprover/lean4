// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.DSimp
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Elab.Tactic.Grind.DSimprocDSL import Lean.Meta.Sym.DSimp.Variant import Lean.Meta.Sym.DSimp.Reduce import Lean.Meta.Sym.DSimp.DSimproc
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_ofArray(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown identifier `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "invalid `dsimp` arguments, local declarations and `*` have been provided"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_evalGround___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unknown Sym.dsimp variant `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`Sym.dsimp` made no progress"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symDSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(48, 250, 158, 59, 57, 156, 255, 54)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "DSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 179, 218, 147, 248, 180, 79, 149)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(195, 192, 13, 213, 61, 30, 178, 142)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(142, 130, 0, 181, 249, 18, 192, 91)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(28, 126, 204, 224, 120, 236, 4, 195)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(153, 15, 247, 82, 172, 98, 243, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(151, 137, 186, 241, 57, 190, 170, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalSymDSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(121, 121, 210, 219, 157, 158, 137, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__2));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__4));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(lean_object* v___x_56_, lean_object* v_as_57_, size_t v_sz_58_, size_t v_i_59_, lean_object* v_b_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_a_71_; uint8_t v___x_75_; 
v___x_75_ = lean_usize_dec_lt(v_i_59_, v_sz_58_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v_b_60_);
return v___x_76_;
}
else
{
lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_115_; 
v_fst_77_ = lean_ctor_get(v_b_60_, 0);
v_snd_78_ = lean_ctor_get(v_b_60_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_b_60_);
if (v_isSharedCheck_115_ == 0)
{
v___x_80_ = v_b_60_;
v_isShared_81_ = v_isSharedCheck_115_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snd_78_);
lean_inc(v_fst_77_);
lean_dec(v_b_60_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_115_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_a_82_ = lean_array_uget_borrowed(v_as_57_, v_i_59_);
lean_inc(v_a_82_);
v___x_83_ = l_Lean_Syntax_getKind(v_a_82_);
v___x_84_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1));
v___x_85_ = lean_name_eq(v___x_83_, v___x_84_);
lean_dec(v___x_83_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_88_; 
lean_dec(v_snd_78_);
v___x_86_ = lean_box(v___x_75_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_86_);
v___x_88_ = v___x_80_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_fst_77_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
v_a_71_ = v___x_88_;
goto v___jp_70_;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = l_Lean_Syntax_getId(v_a_82_);
v___x_91_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_56_, v___x_90_);
if (lean_obj_tag(v___x_91_) == 1)
{
lean_object* v_val_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_dec(v___x_90_);
v_val_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_92_);
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = l_Lean_LocalDecl_fvarId(v_val_92_);
lean_dec(v_val_92_);
v___x_94_ = lean_array_push(v_fst_77_, v___x_93_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_94_);
v___x_96_ = v___x_80_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_snd_78_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
v_a_71_ = v___x_96_;
goto v___jp_70_;
}
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v___x_91_);
v___x_98_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__3);
v___x_99_ = l_Lean_MessageData_ofName(v___x_90_);
v___x_100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5);
v___x_102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_102_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_105_; 
lean_dec_ref_known(v___x_103_, 1);
if (v_isShared_81_ == 0)
{
v___x_105_ = v___x_80_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_fst_77_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_snd_78_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
v_a_71_ = v___x_105_;
goto v___jp_70_;
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_del_object(v___x_80_);
lean_dec(v_snd_78_);
lean_dec(v_fst_77_);
v_a_107_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_103_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_103_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
}
v___jp_70_:
{
size_t v___x_72_; size_t v___x_73_; 
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_add(v_i_59_, v___x_72_);
v_i_59_ = v___x_73_;
v_b_60_ = v_a_71_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___boxed(lean_object* v___x_116_, lean_object* v_as_117_, lean_object* v_sz_118_, lean_object* v_i_119_, lean_object* v_b_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
size_t v_sz_boxed_130_; size_t v_i_boxed_131_; lean_object* v_res_132_; 
v_sz_boxed_130_ = lean_unbox_usize(v_sz_118_);
lean_dec(v_sz_118_);
v_i_boxed_131_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_res_132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(v___x_116_, v_as_117_, v_sz_boxed_130_, v_i_boxed_131_, v_b_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec_ref(v_as_117_);
lean_dec_ref(v___x_116_);
return v_res_132_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(lean_object* v_args_x3f_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
if (lean_obj_tag(v_args_x3f_145_) == 1)
{
lean_object* v_val_155_; lean_object* v_lctx_156_; lean_object* v___x_157_; lean_object* v___x_158_; size_t v_sz_159_; size_t v___x_160_; lean_object* v___x_161_; 
v_val_155_ = lean_ctor_get(v_args_x3f_145_, 0);
v_lctx_156_ = lean_ctor_get(v_a_150_, 2);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1));
v_sz_159_ = lean_array_size(v_val_155_);
v___x_160_ = ((size_t)0ULL);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(v_lctx_156_, v_val_155_, v_sz_159_, v___x_160_, v___x_158_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_187_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_187_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_187_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_187_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_fst_166_ = lean_ctor_get(v_a_162_, 0);
lean_inc(v_fst_166_);
v_snd_167_ = lean_ctor_get(v_a_162_, 1);
lean_inc(v_snd_167_);
lean_dec(v_a_162_);
v___x_174_ = lean_array_get_size(v_fst_166_);
v___x_175_ = lean_nat_dec_eq(v___x_174_, v___x_157_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_unbox(v_snd_167_);
if (v___x_176_ == 0)
{
goto v___jp_168_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_snd_167_);
lean_dec(v_fst_166_);
lean_del_object(v___x_164_);
v___x_177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3);
v___x_178_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_177_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
goto v___jp_168_;
}
v___jp_168_:
{
lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_172_; 
v___x_169_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_169_, 0, v_fst_166_);
v___x_170_ = lean_unbox(v_snd_167_);
lean_dec(v_snd_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_170_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_169_);
v___x_172_ = v___x_164_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_169_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_161_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_161_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4));
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___boxed(lean_object* v_args_x3f_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v_args_x3f_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_args_x3f_198_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object* v_00_u03b1_209_, lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v_msg_210_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object* v_00_u03b1_221_, lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(v_00_u03b1_221_, v_msg_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(lean_object* v_fvarIds_233_, lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = l_Lean_FVarIdSet_ofArray(v_fvarIds_233_);
v___x_247_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v___x_246_, v___y_235_, v___y_241_, v___y_243_, v___y_244_);
lean_dec(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0___boxed(lean_object* v_fvarIds_248_, lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(v_fvarIds_248_, v_x_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v_fvarIds_248_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1(lean_object* v_pre_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc_ref(v___y_269_);
lean_inc_ref(v___y_263_);
v___x_274_ = lean_apply_11(v_pre_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, lean_box(0));
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
if (lean_obj_tag(v_a_275_) == 0)
{
uint8_t v_done_276_; 
v_done_276_ = lean_ctor_get_uint8(v_a_275_, 0);
lean_dec_ref_known(v_a_275_, 0);
if (v_done_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref_known(v___x_274_, 1);
v___x_277_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_263_, v___y_269_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v___y_269_);
return v___x_277_;
}
else
{
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v___y_269_);
lean_dec_ref(v___y_263_);
return v___x_274_;
}
}
else
{
uint8_t v_done_278_; 
lean_dec_ref(v___y_263_);
v_done_278_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*1);
if (v_done_278_ == 0)
{
lean_object* v_e_x27_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref_known(v___x_274_, 1);
v_e_x27_279_ = lean_ctor_get(v_a_275_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_297_ == 0)
{
v___x_281_ = v_a_275_;
v_isShared_282_ = v_isSharedCheck_297_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_e_x27_279_);
lean_dec(v_a_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_297_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; 
lean_inc_ref(v_e_x27_279_);
v___x_283_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_279_, v___y_269_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v___y_269_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
if (lean_obj_tag(v_a_284_) == 0)
{
lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_283_, 0);
lean_dec(v_unused_296_);
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_295_;
goto v_resetjp_285_;
}
else
{
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_295_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint8_t v_done_288_; lean_object* v___x_290_; 
v_done_288_ = lean_ctor_get_uint8(v_a_284_, 0);
lean_dec_ref_known(v_a_284_, 0);
if (v_isShared_282_ == 0)
{
v___x_290_ = v___x_281_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_e_x27_279_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_292_; 
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v_done_288_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_290_);
v___x_292_ = v___x_286_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_284_, 1);
lean_del_object(v___x_281_);
lean_dec_ref(v_e_x27_279_);
return v___x_283_;
}
}
else
{
lean_del_object(v___x_281_);
lean_dec_ref(v_e_x27_279_);
return v___x_283_;
}
}
}
else
{
lean_dec_ref_known(v_a_275_, 1);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v___y_269_);
return v___x_274_;
}
}
}
else
{
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v___y_269_);
lean_dec_ref(v___y_263_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1___boxed(lean_object* v_pre_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1(v_pre_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(lean_object* v_pre_311_, lean_object* v_args_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_fvarIds_324_; uint8_t v_zetaDeltaAll_325_; lean_object* v_pre_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; 
v_fvarIds_324_ = lean_ctor_get(v_args_312_, 0);
v_zetaDeltaAll_325_ = lean_ctor_get_uint8(v_args_312_, sizeof(void*)*1);
if (v_zetaDeltaAll_325_ == 0)
{
v_pre_327_ = v_pre_311_;
v___y_328_ = v_a_313_;
v___y_329_ = v_a_314_;
v___y_330_ = v_a_315_;
v___y_331_ = v_a_316_;
v___y_332_ = v_a_317_;
v___y_333_ = v_a_318_;
v___y_334_ = v_a_319_;
v___y_335_ = v_a_320_;
v___y_336_ = v_a_321_;
v___y_337_ = v_a_322_;
goto v___jp_326_;
}
else
{
lean_object* v_pre_367_; 
v_pre_367_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1___boxed), 12, 1);
lean_closure_set(v_pre_367_, 0, v_pre_311_);
v_pre_327_ = v_pre_367_;
v___y_328_ = v_a_313_;
v___y_329_ = v_a_314_;
v___y_330_ = v_a_315_;
v___y_331_ = v_a_316_;
v___y_332_ = v_a_317_;
v___y_333_ = v_a_318_;
v___y_334_ = v_a_319_;
v___y_335_ = v_a_320_;
v___y_336_ = v_a_321_;
v___y_337_ = v_a_322_;
goto v___jp_326_;
}
v___jp_326_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_array_get_size(v_fvarIds_324_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_inc(v___y_337_);
lean_inc_ref(v___y_336_);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
v___x_341_ = lean_apply_11(v_pre_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, lean_box(0));
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
v___x_343_ = lean_box(0);
if (lean_obj_tag(v_a_342_) == 0)
{
uint8_t v_done_344_; 
v_done_344_ = lean_ctor_get_uint8(v_a_342_, 0);
lean_dec_ref_known(v_a_342_, 0);
if (v_done_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref_known(v___x_341_, 1);
v___x_345_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(v_fvarIds_324_, v___x_343_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_345_;
}
else
{
lean_dec_ref(v___y_328_);
return v___x_341_;
}
}
else
{
uint8_t v_done_346_; 
lean_dec_ref(v___y_328_);
v_done_346_ = lean_ctor_get_uint8(v_a_342_, sizeof(void*)*1);
if (v_done_346_ == 0)
{
lean_object* v_e_x27_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref_known(v___x_341_, 1);
v_e_x27_347_ = lean_ctor_get(v_a_342_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_365_ == 0)
{
v___x_349_ = v_a_342_;
v_isShared_350_ = v_isSharedCheck_365_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_e_x27_347_);
lean_dec(v_a_342_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_365_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; 
lean_inc_ref(v_e_x27_347_);
v___x_351_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(v_fvarIds_324_, v___x_343_, v_e_x27_347_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
if (lean_obj_tag(v_a_352_) == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_363_; 
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v___x_351_, 0);
lean_dec(v_unused_364_);
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
else
{
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
uint8_t v_done_356_; lean_object* v___x_358_; 
v_done_356_ = lean_ctor_get_uint8(v_a_352_, 0);
lean_dec_ref_known(v_a_352_, 0);
if (v_isShared_350_ == 0)
{
v___x_358_ = v___x_349_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_e_x27_347_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*1, v_done_356_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_358_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_352_, 1);
lean_del_object(v___x_349_);
lean_dec_ref(v_e_x27_347_);
return v___x_351_;
}
}
else
{
lean_del_object(v___x_349_);
lean_dec_ref(v_e_x27_347_);
return v___x_351_;
}
}
}
else
{
lean_dec_ref_known(v_a_342_, 1);
return v___x_341_;
}
}
}
else
{
lean_dec_ref(v___y_328_);
return v___x_341_;
}
}
else
{
lean_object* v___x_366_; 
lean_inc(v___y_337_);
lean_inc_ref(v___y_336_);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
v___x_366_ = lean_apply_11(v_pre_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, lean_box(0));
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed(lean_object* v_pre_368_, lean_object* v_args_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(v_pre_368_, v_args_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_args_369_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
lean_inc_ref(v___y_383_);
v___x_394_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
if (lean_obj_tag(v_a_395_) == 0)
{
uint8_t v_done_396_; 
v_done_396_ = lean_ctor_get_uint8(v_a_395_, 0);
lean_dec_ref_known(v_a_395_, 0);
if (v_done_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref_known(v___x_394_, 1);
v___x_397_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_383_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec_ref(v___y_383_);
return v___x_397_;
}
else
{
lean_dec_ref(v___y_383_);
return v___x_394_;
}
}
else
{
uint8_t v_done_398_; 
lean_dec_ref(v___y_383_);
v_done_398_ = lean_ctor_get_uint8(v_a_395_, sizeof(void*)*1);
if (v_done_398_ == 0)
{
lean_object* v_e_x27_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref_known(v___x_394_, 1);
v_e_x27_399_ = lean_ctor_get(v_a_395_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_417_ == 0)
{
v___x_401_ = v_a_395_;
v_isShared_402_ = v_isSharedCheck_417_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_e_x27_399_);
lean_dec(v_a_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_417_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_399_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
if (lean_obj_tag(v_a_404_) == 0)
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_415_; 
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_416_);
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
else
{
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v_done_408_; lean_object* v___x_410_; 
v_done_408_ = lean_ctor_get_uint8(v_a_404_, 0);
lean_dec_ref_known(v_a_404_, 0);
if (v_isShared_402_ == 0)
{
v___x_410_ = v___x_401_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_e_x27_399_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v_done_408_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_410_);
v___x_412_ = v___x_406_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_404_, 1);
lean_del_object(v___x_401_);
lean_dec_ref(v_e_x27_399_);
return v___x_403_;
}
}
else
{
lean_del_object(v___x_401_);
lean_dec_ref(v_e_x27_399_);
return v___x_403_;
}
}
}
else
{
lean_dec_ref_known(v_a_395_, 1);
return v___x_394_;
}
}
}
else
{
lean_dec_ref(v___y_383_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0___boxed(lean_object* v_x_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(v_x_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(lean_object* v___f_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
lean_inc_ref(v___y_432_);
v___x_443_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_432_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
v___x_445_ = lean_box(0);
if (lean_obj_tag(v_a_444_) == 0)
{
uint8_t v_done_446_; 
v_done_446_ = lean_ctor_get_uint8(v_a_444_, 0);
lean_dec_ref_known(v_a_444_, 0);
if (v_done_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref_known(v___x_443_, 1);
v___x_447_ = lean_apply_12(v___f_431_, v___x_445_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, lean_box(0));
return v___x_447_;
}
else
{
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec_ref(v___f_431_);
return v___x_443_;
}
}
else
{
uint8_t v_done_448_; 
lean_dec_ref(v___y_432_);
v_done_448_ = lean_ctor_get_uint8(v_a_444_, sizeof(void*)*1);
if (v_done_448_ == 0)
{
lean_object* v_e_x27_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref_known(v___x_443_, 1);
v_e_x27_449_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_467_ == 0)
{
v___x_451_ = v_a_444_;
v_isShared_452_ = v_isSharedCheck_467_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_e_x27_449_);
lean_dec(v_a_444_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_467_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; 
lean_inc_ref(v_e_x27_449_);
v___x_453_ = lean_apply_12(v___f_431_, v___x_445_, v_e_x27_449_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, lean_box(0));
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
if (lean_obj_tag(v_a_454_) == 0)
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_465_; 
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___x_453_, 0);
lean_dec(v_unused_466_);
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v_done_458_; lean_object* v___x_460_; 
v_done_458_ = lean_ctor_get_uint8(v_a_454_, 0);
lean_dec_ref_known(v_a_454_, 0);
if (v_isShared_452_ == 0)
{
v___x_460_ = v___x_451_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_e_x27_449_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*1, v_done_458_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_460_);
v___x_462_ = v___x_456_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_454_, 1);
lean_del_object(v___x_451_);
lean_dec_ref(v_e_x27_449_);
return v___x_453_;
}
}
else
{
lean_del_object(v___x_451_);
lean_dec_ref(v_e_x27_449_);
return v___x_453_;
}
}
}
else
{
lean_dec_ref_known(v_a_444_, 1);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___f_431_);
return v___x_443_;
}
}
}
else
{
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec_ref(v___f_431_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1___boxed(lean_object* v___f_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(v___f_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(lean_object* v_args_486_){
_start:
{
lean_object* v_pre_488_; lean_object* v_pre_489_; lean_object* v_post_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_pre_488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1));
v_pre_489_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed), 13, 2);
lean_closure_set(v_pre_489_, 0, v_pre_488_);
lean_closure_set(v_pre_489_, 1, v_args_486_);
v_post_490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2));
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_pre_489_);
lean_ctor_set(v___x_491_, 1, v_post_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___boxed(lean_object* v_args_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(lean_object* v_args_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_496_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___boxed(lean_object* v_args_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(v_args_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg(){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0));
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___boxed(lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed(lean_object* v_x_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(v_x_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_x_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(lean_object* v_stx_x3f_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
if (lean_obj_tag(v_stx_x3f_549_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_560_; 
v_val_559_ = lean_ctor_get(v_stx_x3f_549_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_stx_x3f_549_, 1);
v___x_560_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(v_val_559_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_stx_x3f_549_);
v___x_561_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed), 11, 0);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc___boxed(lean_object* v_stx_x3f_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_stx_x3f_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_573_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(lean_object* v_variantName_580_, lean_object* v_args_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = l_Lean_Name_isAnonymous(v_variantName_580_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v_env_593_; lean_object* v___x_594_; 
v___x_592_ = lean_st_ref_get(v_a_589_);
v_env_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_ref(v_env_593_);
lean_dec(v___x_592_);
v___x_594_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_593_, v_variantName_580_);
if (lean_obj_tag(v___x_594_) == 1)
{
lean_object* v_val_595_; lean_object* v_pre_x3f_596_; lean_object* v_post_x3f_597_; lean_object* v_config_598_; lean_object* v___x_599_; 
lean_dec(v_variantName_580_);
v_val_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v___x_594_, 1);
v_pre_x3f_596_ = lean_ctor_get(v_val_595_, 0);
lean_inc(v_pre_x3f_596_);
v_post_x3f_597_ = lean_ctor_get(v_val_595_, 1);
lean_inc(v_post_x3f_597_);
v_config_598_ = lean_ctor_get(v_val_595_, 2);
lean_inc_ref(v_config_598_);
lean_dec(v_val_595_);
v___x_599_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_pre_x3f_596_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_post_x3f_597_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_612_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_612_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_606_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed), 13, 2);
lean_closure_set(v___x_606_, 0, v_a_600_);
lean_closure_set(v___x_606_, 1, v_args_581_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v_a_602_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_config_598_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_608_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_600_);
lean_dec_ref(v_config_598_);
lean_dec_ref(v_args_581_);
v_a_613_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_601_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_601_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_config_598_);
lean_dec(v_post_x3f_597_);
lean_dec_ref(v_args_581_);
v_a_621_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_599_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_599_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___x_594_);
lean_dec_ref(v_args_581_);
v___x_629_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1);
v___x_630_ = l_Lean_MessageData_ofName(v_variantName_580_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_633_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_634_;
}
}
else
{
lean_object* v___x_635_; lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_variantName_580_);
v___x_635_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_581_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2));
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_a_636_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___boxed(lean_object* v_variantName_646_, lean_object* v_args_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v_variantName_646_, v_args_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
return v_res_657_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_box(0);
v___x_659_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg(){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0);
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___boxed(lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(lean_object* v_00_u03b1_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___boxed(lean_object* v_00_u03b1_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(v_00_u03b1_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(lean_object* v_x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
v___x_699_ = lean_apply_10(v_x_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, lean_box(0));
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed(lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(lean_object* v_mvarId_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___f_724_; lean_object* v___x_725_; 
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_724_, 0, v_x_713_);
lean_closure_set(v___f_724_, 1, v___y_714_);
lean_closure_set(v___f_724_, 2, v___y_715_);
lean_closure_set(v___f_724_, 3, v___y_716_);
lean_closure_set(v___f_724_, 4, v___y_717_);
lean_closure_set(v___f_724_, 5, v___y_718_);
v___x_725_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_712_, v___f_724_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_725_) == 0)
{
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___boxed(lean_object* v_mvarId_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_734_, v_x_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(lean_object* v_00_u03b1_747_, lean_object* v_mvarId_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_748_, v_x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed(lean_object* v_00_u03b1_761_, lean_object* v_mvarId_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(v_00_u03b1_761_, v_mvarId_762_, v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(lean_object* v_mvarId_775_, lean_object* v_fst_776_, lean_object* v_snd_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_MVarId_getType(v_mvarId_775_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_791_, 0, v_a_790_);
v___x_792_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_791_, v_fst_776_, v_snd_777_, v___y_778_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_792_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v___y_778_);
lean_dec_ref(v_snd_777_);
lean_dec_ref(v_fst_776_);
v_a_793_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_789_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed(lean_object* v_mvarId_801_, lean_object* v_fst_802_, lean_object* v_snd_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(v_mvarId_801_, v_fst_802_, v_snd_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7(uint8_t v___x_816_, uint8_t v___x_817_, lean_object* v_as_818_, size_t v_i_819_, size_t v_stop_820_, lean_object* v_b_821_){
_start:
{
lean_object* v___y_823_; uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_eq(v_i_819_, v_stop_820_);
if (v___x_827_ == 0)
{
lean_object* v_fst_828_; uint8_t v___x_829_; 
v_fst_828_ = lean_ctor_get(v_b_821_, 0);
v___x_829_ = lean_unbox(v_fst_828_);
if (v___x_829_ == 0)
{
lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_snd_830_ = lean_ctor_get(v_b_821_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_821_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_b_821_, 0);
lean_dec(v_unused_839_);
v___x_832_ = v_b_821_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_dec(v_b_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_box(v___x_816_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_snd_830_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v___y_823_ = v___x_836_;
goto v___jp_822_;
}
}
}
else
{
lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_850_; 
v_snd_840_ = lean_ctor_get(v_b_821_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_b_821_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_b_821_, 0);
lean_dec(v_unused_851_);
v___x_842_ = v_b_821_;
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_dec(v_b_821_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_844_ = lean_array_uget_borrowed(v_as_818_, v_i_819_);
lean_inc(v___x_844_);
v___x_845_ = lean_array_push(v_snd_840_, v___x_844_);
v___x_846_ = lean_box(v___x_817_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_845_);
lean_ctor_set(v___x_842_, 0, v___x_846_);
v___x_848_ = v___x_842_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_845_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v___y_823_ = v___x_848_;
goto v___jp_822_;
}
}
}
}
else
{
return v_b_821_;
}
v___jp_822_:
{
size_t v___x_824_; size_t v___x_825_; 
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_i_819_, v___x_824_);
v_i_819_ = v___x_825_;
v_b_821_ = v___y_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7___boxed(lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v_as_854_, lean_object* v_i_855_, lean_object* v_stop_856_, lean_object* v_b_857_){
_start:
{
uint8_t v___x_13202__boxed_858_; uint8_t v___x_13203__boxed_859_; size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v___x_13202__boxed_858_ = lean_unbox(v___x_852_);
v___x_13203__boxed_859_ = lean_unbox(v___x_853_);
v_i_boxed_860_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_856_);
lean_dec(v_stop_856_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7(v___x_13202__boxed_858_, v___x_13203__boxed_859_, v_as_854_, v_i_boxed_860_, v_stop_boxed_861_, v_b_857_);
lean_dec_ref(v_as_854_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg(lean_object* v_m_863_, lean_object* v_query_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_zero_868_; uint8_t v_isZero_869_; 
v_zero_868_ = lean_unsigned_to_nat(0u);
v_isZero_869_ = lean_nat_dec_eq(v_x_866_, v_zero_868_);
if (v_isZero_869_ == 1)
{
lean_dec(v_x_867_);
lean_dec(v_x_866_);
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_box(2);
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_val_871_ = lean_ctor_get(v_x_865_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v_x_865_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_val_871_);
lean_dec(v_x_865_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_val_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_keyArray_879_; lean_object* v_valueArray_880_; lean_object* v___x_881_; uint8_t v_isSome_882_; 
v_keyArray_879_ = lean_ctor_get(v_m_863_, 1);
v_valueArray_880_ = lean_ctor_get(v_m_863_, 2);
v___x_881_ = lean_array_fget_borrowed(v_keyArray_879_, v_x_867_);
v_isSome_882_ = lean_noption_is_some(v___x_881_);
if (v_isSome_882_ == 0)
{
lean_dec(v_x_866_);
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v_x_867_);
return v___x_883_;
}
else
{
lean_object* v_val_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_x_867_);
v_val_884_ = lean_ctor_get(v_x_865_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v_x_865_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_val_884_);
lean_dec(v_x_865_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_val_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_one_892_; lean_object* v_n_893_; lean_object* v___y_895_; 
v_one_892_ = lean_unsigned_to_nat(1u);
v_n_893_ = lean_nat_sub(v_x_866_, v_one_892_);
lean_dec(v_x_866_);
if (v_isSome_882_ == 0)
{
goto v___jp_901_;
}
else
{
lean_object* v___x_903_; uint8_t v_isSome_904_; 
v___x_903_ = lean_array_fget_borrowed(v_valueArray_880_, v_x_867_);
v_isSome_904_ = lean_noption_is_some(v___x_903_);
if (v_isSome_904_ == 0)
{
goto v___jp_901_;
}
else
{
lean_object* v_val_905_; uint8_t v___x_906_; 
lean_inc(v___x_881_);
v_val_905_ = lean_noption_get(v___x_881_);
v___x_906_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_val_905_, v_query_864_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
lean_dec(v_val_905_);
v___x_907_ = lean_array_get_size(v_keyArray_879_);
v___x_908_ = lean_nat_add(v_x_867_, v_one_892_);
lean_dec(v_x_867_);
v___x_909_ = lean_nat_dec_lt(v___x_908_, v___x_907_);
if (v___x_909_ == 0)
{
lean_dec(v___x_908_);
v_x_866_ = v_n_893_;
v_x_867_ = v_zero_868_;
goto _start;
}
else
{
v_x_866_ = v_n_893_;
v_x_867_ = v___x_908_;
goto _start;
}
}
else
{
lean_object* v_val_912_; lean_object* v___x_913_; 
lean_dec(v_n_893_);
lean_dec(v_x_865_);
lean_inc(v___x_903_);
v_val_912_ = lean_noption_get(v___x_903_);
v___x_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_913_, 0, v_x_867_);
lean_ctor_set(v___x_913_, 1, v_val_905_);
lean_ctor_set(v___x_913_, 2, v_val_912_);
return v___x_913_;
}
}
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_array_get_size(v_keyArray_879_);
v___x_897_ = lean_nat_add(v_x_867_, v_one_892_);
lean_dec(v_x_867_);
v___x_898_ = lean_nat_dec_lt(v___x_897_, v___x_896_);
if (v___x_898_ == 0)
{
lean_dec(v___x_897_);
v_x_865_ = v___y_895_;
v_x_866_ = v_n_893_;
v_x_867_ = v_zero_868_;
goto _start;
}
else
{
v_x_865_ = v___y_895_;
v_x_866_ = v_n_893_;
v_x_867_ = v___x_897_;
goto _start;
}
}
v___jp_901_:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v___x_902_; 
lean_inc(v_x_867_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v_x_867_);
v___y_895_ = v___x_902_;
goto v___jp_894_;
}
else
{
v___y_895_ = v_x_865_;
goto v___jp_894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg___boxed(lean_object* v_m_914_, lean_object* v_query_915_, lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg(v_m_914_, v_query_915_, v_x_916_, v_x_917_, v_x_918_);
lean_dec_ref(v_query_915_);
lean_dec_ref(v_m_914_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object* v_m_920_, lean_object* v_query_921_){
_start:
{
lean_object* v_keyArray_922_; lean_object* v___x_923_; uint64_t v___x_924_; uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v_fold_927_; uint64_t v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_keyArray_922_ = lean_ctor_get(v_m_920_, 1);
v___x_923_ = lean_array_get_size(v_keyArray_922_);
v___x_924_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_query_921_);
v___x_925_ = 32ULL;
v___x_926_ = lean_uint64_shift_right(v___x_924_, v___x_925_);
v_fold_927_ = lean_uint64_xor(v___x_924_, v___x_926_);
v___x_928_ = 16ULL;
v___x_929_ = lean_uint64_shift_right(v_fold_927_, v___x_928_);
v___x_930_ = lean_uint64_xor(v_fold_927_, v___x_929_);
v___x_931_ = lean_uint64_to_usize(v___x_930_);
v___x_932_ = lean_usize_of_nat(v___x_923_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_sub(v___x_932_, v___x_933_);
v___x_935_ = lean_usize_land(v___x_931_, v___x_934_);
v___x_936_ = lean_usize_to_nat(v___x_935_);
v___x_937_ = lean_box(0);
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg(v_m_920_, v_query_921_, v___x_937_, v___x_923_, v___x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object* v_m_939_, lean_object* v_query_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_m_939_, v_query_940_);
lean_dec_ref(v_query_940_);
lean_dec_ref(v_m_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg(lean_object* v_b_942_, lean_object* v_acc_943_, lean_object* v_i_944_){
_start:
{
lean_object* v___y_946_; lean_object* v_keyArray_954_; lean_object* v_valueArray_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_keyArray_954_ = lean_ctor_get(v_b_942_, 1);
v_valueArray_955_ = lean_ctor_get(v_b_942_, 2);
v___x_956_ = lean_array_get_size(v_keyArray_954_);
v___x_957_ = lean_nat_dec_lt(v_i_944_, v___x_956_);
if (v___x_957_ == 0)
{
lean_dec(v_i_944_);
return v_acc_943_;
}
else
{
lean_object* v___x_958_; uint8_t v_isSome_959_; 
v___x_958_ = lean_array_fget_borrowed(v_keyArray_954_, v_i_944_);
v_isSome_959_ = lean_noption_is_some(v___x_958_);
if (v_isSome_959_ == 0)
{
goto v___jp_950_;
}
else
{
lean_object* v___x_960_; uint8_t v_isSome_961_; 
v___x_960_ = lean_array_fget_borrowed(v_valueArray_955_, v_i_944_);
v_isSome_961_ = lean_noption_is_some(v___x_960_);
if (v_isSome_961_ == 0)
{
goto v___jp_950_;
}
else
{
lean_object* v_val_962_; lean_object* v_val_963_; lean_object* v_i_965_; lean_object* v___x_970_; 
lean_inc(v___x_958_);
v_val_962_ = lean_noption_get(v___x_958_);
lean_inc(v___x_960_);
v_val_963_ = lean_noption_get(v___x_960_);
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_acc_943_, v_val_962_);
switch(lean_obj_tag(v___x_970_))
{
case 0:
{
lean_object* v_index_971_; lean_object* v_size_972_; lean_object* v___x_973_; 
v_index_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_971_);
lean_dec_ref_known(v___x_970_, 3);
v_size_972_ = lean_ctor_get(v_acc_943_, 0);
lean_inc(v_size_972_);
v___x_973_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_943_, v_size_972_, v_index_971_, v_val_962_, v_val_963_);
lean_dec(v_index_971_);
v___y_946_ = v___x_973_;
goto v___jp_945_;
}
case 1:
{
lean_object* v_index_974_; 
v_index_974_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_974_);
lean_dec_ref_known(v___x_970_, 1);
v_i_965_ = v_index_974_;
goto v___jp_964_;
}
default: 
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_943_, v___x_975_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_index_977_; 
v_index_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_977_);
lean_dec_ref_known(v___x_976_, 1);
v_i_965_ = v_index_977_;
goto v___jp_964_;
}
else
{
lean_dec(v_val_963_);
lean_dec(v_val_962_);
v___y_946_ = v_acc_943_;
goto v___jp_945_;
}
}
}
v___jp_964_:
{
lean_object* v_size_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_size_966_ = lean_ctor_get(v_acc_943_, 0);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_size_966_, v___x_967_);
v___x_969_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_943_, v___x_968_, v_i_965_, v_val_962_, v_val_963_);
lean_dec(v_i_965_);
v___y_946_ = v___x_969_;
goto v___jp_945_;
}
}
}
}
v___jp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_i_944_, v___x_947_);
lean_dec(v_i_944_);
v_acc_943_ = v___y_946_;
v_i_944_ = v___x_948_;
goto _start;
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_add(v_i_944_, v___x_951_);
lean_dec(v_i_944_);
v_i_944_ = v___x_952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_b_978_, lean_object* v_acc_979_, lean_object* v_i_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg(v_b_978_, v_acc_979_, v_i_980_);
lean_dec_ref(v_b_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg(lean_object* v_init_982_, lean_object* v_b_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg(v_b_983_, v_init_982_, v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg___boxed(lean_object* v_init_986_, lean_object* v_b_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg(v_init_986_, v_b_987_);
lean_dec_ref(v_b_987_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object* v_m_989_){
_start:
{
lean_object* v_keyArray_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_cellCount_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_target_997_; lean_object* v___x_998_; 
v_keyArray_990_ = lean_ctor_get(v_m_989_, 1);
v___x_991_ = lean_array_get_size(v_keyArray_990_);
v___x_992_ = lean_unsigned_to_nat(2u);
v_cellCount_993_ = lean_nat_mul(v___x_991_, v___x_992_);
v___x_994_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_993_);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_993_);
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_993_);
v_target_997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_997_, 0, v___x_994_);
lean_ctor_set(v_target_997_, 1, v___x_995_);
lean_ctor_set(v_target_997_, 2, v___x_996_);
v___x_998_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg(v_target_997_, v_m_989_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object* v_m_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_999_);
lean_dec_ref(v_m_999_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg(lean_object* v_m_1001_, lean_object* v_query_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_m_1001_, v_query_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_index_1004_; lean_object* v_key_1005_; lean_object* v_value_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_index_1004_ = lean_ctor_get(v___x_1003_, 0);
v_key_1005_ = lean_ctor_get(v___x_1003_, 1);
v_value_1006_ = lean_ctor_get(v___x_1003_, 2);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1003_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_value_1006_);
lean_inc(v_key_1005_);
lean_inc(v_index_1004_);
lean_dec(v___x_1003_);
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
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_index_1004_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_key_1005_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_value_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v___x_1014_; 
lean_dec(v___x_1003_);
v___x_1014_ = lean_box(1);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg___boxed(lean_object* v_m_1015_, lean_object* v_query_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg(v_m_1015_, v_query_1016_);
lean_dec_ref(v_query_1016_);
lean_dec_ref(v_m_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg(lean_object* v_m_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg(v_m_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_value_1021_; lean_object* v___x_1022_; 
v_value_1021_ = lean_ctor_get(v___x_1020_, 2);
lean_inc(v_value_1021_);
lean_dec_ref_known(v___x_1020_, 3);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_value_1021_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(0);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg___boxed(lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg(v_m_1024_, v_a_1025_);
lean_dec_ref(v_a_1025_);
lean_dec_ref(v_m_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
lean_object* v_ks_1031_; lean_object* v_vs_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1056_; 
v_ks_1031_ = lean_ctor_get(v_x_1027_, 0);
v_vs_1032_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1034_ = v_x_1027_;
v_isShared_1035_ = v_isSharedCheck_1056_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_vs_1032_);
lean_inc(v_ks_1031_);
lean_dec(v_x_1027_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1056_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = lean_array_get_size(v_ks_1031_);
v___x_1037_ = lean_nat_dec_lt(v_x_1028_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec(v_x_1028_);
v___x_1038_ = lean_array_push(v_ks_1031_, v_x_1029_);
v___x_1039_ = lean_array_push(v_vs_1032_, v_x_1030_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1039_);
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1041_ = v___x_1034_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
else
{
lean_object* v_k_x27_1043_; uint8_t v___x_1044_; 
v_k_x27_1043_ = lean_array_fget_borrowed(v_ks_1031_, v_x_1028_);
v___x_1044_ = l_Lean_instBEqMVarId_beq(v_x_1029_, v_k_x27_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1046_; 
if (v_isShared_1035_ == 0)
{
v___x_1046_ = v___x_1034_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_ks_1031_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_vs_1032_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_nat_add(v_x_1028_, v___x_1047_);
lean_dec(v_x_1028_);
v_x_1027_ = v___x_1046_;
v_x_1028_ = v___x_1048_;
goto _start;
}
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1051_ = lean_array_fset(v_ks_1031_, v_x_1028_, v_x_1029_);
v___x_1052_ = lean_array_fset(v_vs_1032_, v_x_1028_, v_x_1030_);
lean_dec(v_x_1028_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1052_);
lean_ctor_set(v___x_1034_, 0, v___x_1051_);
v___x_1054_ = v___x_1034_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1052_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_n_1057_, lean_object* v_k_1058_, lean_object* v_v_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1057_, v___x_1060_, v_k_1058_, v_v_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(lean_object* v_x_1063_, size_t v_x_1064_, size_t v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v_es_1068_; size_t v___x_1069_; size_t v___x_1070_; lean_object* v_j_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_es_1068_ = lean_ctor_get(v_x_1063_, 0);
v___x_1069_ = ((size_t)31ULL);
v___x_1070_ = lean_usize_land(v_x_1064_, v___x_1069_);
v_j_1071_ = lean_usize_to_nat(v___x_1070_);
v___x_1072_ = lean_array_get_size(v_es_1068_);
v___x_1073_ = lean_nat_dec_lt(v_j_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v_j_1071_);
lean_dec(v_x_1067_);
lean_dec(v_x_1066_);
return v_x_1063_;
}
else
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1112_; 
lean_inc_ref(v_es_1068_);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v_x_1063_, 0);
lean_dec(v_unused_1113_);
v___x_1075_ = v_x_1063_;
v_isShared_1076_ = v_isSharedCheck_1112_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v_x_1063_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1112_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_v_1077_; lean_object* v___x_1078_; lean_object* v_xs_x27_1079_; lean_object* v___y_1081_; 
v_v_1077_ = lean_array_fget(v_es_1068_, v_j_1071_);
v___x_1078_ = lean_box(0);
v_xs_x27_1079_ = lean_array_fset(v_es_1068_, v_j_1071_, v___x_1078_);
switch(lean_obj_tag(v_v_1077_))
{
case 0:
{
lean_object* v_key_1086_; lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1097_; 
v_key_1086_ = lean_ctor_get(v_v_1077_, 0);
v_val_1087_ = lean_ctor_get(v_v_1077_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_v_1077_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1089_ = v_v_1077_;
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_inc(v_key_1086_);
lean_dec(v_v_1077_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = l_Lean_instBEqMVarId_beq(v_x_1066_, v_key_1086_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_del_object(v___x_1089_);
v___x_1092_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1086_, v_val_1087_, v_x_1066_, v_x_1067_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
v___y_1081_ = v___x_1093_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1095_; 
lean_dec(v_val_1087_);
lean_dec(v_key_1086_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_x_1067_);
lean_ctor_set(v___x_1089_, 0, v_x_1066_);
v___x_1095_ = v___x_1089_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_x_1066_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_x_1067_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1081_ = v___x_1095_;
goto v___jp_1080_;
}
}
}
}
case 1:
{
lean_object* v_node_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1110_; 
v_node_1098_ = lean_ctor_get(v_v_1077_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_v_1077_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1100_ = v_v_1077_;
v_isShared_1101_ = v_isSharedCheck_1110_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_node_1098_);
lean_dec(v_v_1077_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1110_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1102_ = ((size_t)5ULL);
v___x_1103_ = lean_usize_shift_right(v_x_1064_, v___x_1102_);
v___x_1104_ = ((size_t)1ULL);
v___x_1105_ = lean_usize_add(v_x_1065_, v___x_1104_);
v___x_1106_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(v_node_1098_, v___x_1103_, v___x_1105_, v_x_1066_, v_x_1067_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1106_);
v___x_1108_ = v___x_1100_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v___y_1081_ = v___x_1108_;
goto v___jp_1080_;
}
}
}
default: 
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_x_1066_);
lean_ctor_set(v___x_1111_, 1, v_x_1067_);
v___y_1081_ = v___x_1111_;
goto v___jp_1080_;
}
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_array_fset(v_xs_x27_1079_, v_j_1071_, v___y_1081_);
lean_dec(v_j_1071_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1082_);
v___x_1084_ = v___x_1075_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_ks_1114_; lean_object* v_vs_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1135_; 
v_ks_1114_ = lean_ctor_get(v_x_1063_, 0);
v_vs_1115_ = lean_ctor_get(v_x_1063_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1117_ = v_x_1063_;
v_isShared_1118_ = v_isSharedCheck_1135_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_vs_1115_);
lean_inc(v_ks_1114_);
lean_dec(v_x_1063_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1135_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_ks_1114_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_vs_1115_);
v___x_1120_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v_newNode_1121_; uint8_t v___y_1123_; size_t v___x_1129_; uint8_t v___x_1130_; 
v_newNode_1121_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9___redArg(v___x_1120_, v_x_1066_, v_x_1067_);
v___x_1129_ = ((size_t)7ULL);
v___x_1130_ = lean_usize_dec_le(v___x_1129_, v_x_1065_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1121_);
v___x_1132_ = lean_unsigned_to_nat(4u);
v___x_1133_ = lean_nat_dec_lt(v___x_1131_, v___x_1132_);
lean_dec(v___x_1131_);
v___y_1123_ = v___x_1133_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___x_1130_;
goto v___jp_1122_;
}
v___jp_1122_:
{
if (v___y_1123_ == 0)
{
lean_object* v_ks_1124_; lean_object* v_vs_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_ks_1124_ = lean_ctor_get(v_newNode_1121_, 0);
lean_inc_ref(v_ks_1124_);
v_vs_1125_ = lean_ctor_get(v_newNode_1121_, 1);
lean_inc_ref(v_vs_1125_);
lean_dec_ref(v_newNode_1121_);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___closed__0);
v___x_1128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg(v_x_1065_, v_ks_1124_, v_vs_1125_, v___x_1126_, v___x_1127_);
lean_dec_ref(v_vs_1125_);
lean_dec_ref(v_ks_1124_);
return v___x_1128_;
}
else
{
return v_newNode_1121_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg(size_t v_depth_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_i_1139_, lean_object* v_entries_1140_){
_start:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_array_get_size(v_keys_1137_);
v___x_1142_ = lean_nat_dec_lt(v_i_1139_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec(v_i_1139_);
return v_entries_1140_;
}
else
{
lean_object* v_k_1143_; lean_object* v_v_1144_; uint64_t v___x_1145_; size_t v_h_1146_; size_t v___x_1147_; lean_object* v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; size_t v_h_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_k_1143_ = lean_array_fget_borrowed(v_keys_1137_, v_i_1139_);
v_v_1144_ = lean_array_fget_borrowed(v_vals_1138_, v_i_1139_);
v___x_1145_ = l_Lean_instHashableMVarId_hash(v_k_1143_);
v_h_1146_ = lean_uint64_to_usize(v___x_1145_);
v___x_1147_ = ((size_t)5ULL);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_sub(v_depth_1136_, v___x_1149_);
v___x_1151_ = lean_usize_mul(v___x_1147_, v___x_1150_);
v_h_1152_ = lean_usize_shift_right(v_h_1146_, v___x_1151_);
v___x_1153_ = lean_nat_add(v_i_1139_, v___x_1148_);
lean_dec(v_i_1139_);
lean_inc(v_v_1144_);
lean_inc(v_k_1143_);
v___x_1154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(v_entries_1140_, v_h_1152_, v_depth_1136_, v_k_1143_, v_v_1144_);
v_i_1139_ = v___x_1153_;
v_entries_1140_ = v___x_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_depth_1156_, lean_object* v_keys_1157_, lean_object* v_vals_1158_, lean_object* v_i_1159_, lean_object* v_entries_1160_){
_start:
{
size_t v_depth_boxed_1161_; lean_object* v_res_1162_; 
v_depth_boxed_1161_ = lean_unbox_usize(v_depth_1156_);
lean_dec(v_depth_1156_);
v_res_1162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg(v_depth_boxed_1161_, v_keys_1157_, v_vals_1158_, v_i_1159_, v_entries_1160_);
lean_dec_ref(v_vals_1158_);
lean_dec_ref(v_keys_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
size_t v_x_13565__boxed_1168_; size_t v_x_13566__boxed_1169_; lean_object* v_res_1170_; 
v_x_13565__boxed_1168_ = lean_unbox_usize(v_x_1164_);
lean_dec(v_x_1164_);
v_x_13566__boxed_1169_ = lean_unbox_usize(v_x_1165_);
lean_dec(v_x_1165_);
v_res_1170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(v_x_1163_, v_x_13565__boxed_1168_, v_x_13566__boxed_1169_, v_x_1166_, v_x_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
uint64_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = l_Lean_instHashableMVarId_hash(v_x_1172_);
v___x_1175_ = lean_uint64_to_usize(v___x_1174_);
v___x_1176_ = ((size_t)1ULL);
v___x_1177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(v_x_1171_, v___x_1175_, v___x_1176_, v_x_1172_, v_x_1173_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object* v_mvarId_1178_, lean_object* v_val_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_mctx_1183_; lean_object* v_cache_1184_; lean_object* v_zetaDeltaFVarIds_1185_; lean_object* v_postponed_1186_; lean_object* v_diag_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1216_; 
v___x_1182_ = lean_st_ref_take(v___y_1180_);
v_mctx_1183_ = lean_ctor_get(v___x_1182_, 0);
v_cache_1184_ = lean_ctor_get(v___x_1182_, 1);
v_zetaDeltaFVarIds_1185_ = lean_ctor_get(v___x_1182_, 2);
v_postponed_1186_ = lean_ctor_get(v___x_1182_, 3);
v_diag_1187_ = lean_ctor_get(v___x_1182_, 4);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1189_ = v___x_1182_;
v_isShared_1190_ = v_isSharedCheck_1216_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_diag_1187_);
lean_inc(v_postponed_1186_);
lean_inc(v_zetaDeltaFVarIds_1185_);
lean_inc(v_cache_1184_);
lean_inc(v_mctx_1183_);
lean_dec(v___x_1182_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1216_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_depth_1191_; lean_object* v_levelAssignDepth_1192_; lean_object* v_lmvarCounter_1193_; lean_object* v_mvarCounter_1194_; lean_object* v_lDecls_1195_; lean_object* v_decls_1196_; lean_object* v_userNames_1197_; lean_object* v_lAssignment_1198_; lean_object* v_eAssignment_1199_; lean_object* v_dAssignment_1200_; lean_object* v_instanceTypedMVars_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1215_; 
v_depth_1191_ = lean_ctor_get(v_mctx_1183_, 0);
v_levelAssignDepth_1192_ = lean_ctor_get(v_mctx_1183_, 1);
v_lmvarCounter_1193_ = lean_ctor_get(v_mctx_1183_, 2);
v_mvarCounter_1194_ = lean_ctor_get(v_mctx_1183_, 3);
v_lDecls_1195_ = lean_ctor_get(v_mctx_1183_, 4);
v_decls_1196_ = lean_ctor_get(v_mctx_1183_, 5);
v_userNames_1197_ = lean_ctor_get(v_mctx_1183_, 6);
v_lAssignment_1198_ = lean_ctor_get(v_mctx_1183_, 7);
v_eAssignment_1199_ = lean_ctor_get(v_mctx_1183_, 8);
v_dAssignment_1200_ = lean_ctor_get(v_mctx_1183_, 9);
v_instanceTypedMVars_1201_ = lean_ctor_get(v_mctx_1183_, 10);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_mctx_1183_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1203_ = v_mctx_1183_;
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_instanceTypedMVars_1201_);
lean_inc(v_dAssignment_1200_);
lean_inc(v_eAssignment_1199_);
lean_inc(v_lAssignment_1198_);
lean_inc(v_userNames_1197_);
lean_inc(v_decls_1196_);
lean_inc(v_lDecls_1195_);
lean_inc(v_mvarCounter_1194_);
lean_inc(v_lmvarCounter_1193_);
lean_inc(v_levelAssignDepth_1192_);
lean_inc(v_depth_1191_);
lean_dec(v_mctx_1183_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_eAssignment_1199_, v_mvarId_1178_, v_val_1179_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 8, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_depth_1191_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_levelAssignDepth_1192_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_lmvarCounter_1193_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_mvarCounter_1194_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_lDecls_1195_);
lean_ctor_set(v_reuseFailAlloc_1214_, 5, v_decls_1196_);
lean_ctor_set(v_reuseFailAlloc_1214_, 6, v_userNames_1197_);
lean_ctor_set(v_reuseFailAlloc_1214_, 7, v_lAssignment_1198_);
lean_ctor_set(v_reuseFailAlloc_1214_, 8, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1214_, 9, v_dAssignment_1200_);
lean_ctor_set(v_reuseFailAlloc_1214_, 10, v_instanceTypedMVars_1201_);
v___x_1207_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1207_);
v___x_1209_ = v___x_1189_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_cache_1184_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_zetaDeltaFVarIds_1185_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_postponed_1186_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_diag_1187_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = lean_st_ref_put(v___y_1180_, v___x_1209_);
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg___boxed(lean_object* v_mvarId_1217_, lean_object* v_val_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_mvarId_1217_, v_val_1218_, v___y_1219_);
lean_dec(v___y_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(size_t v_sz_1222_, size_t v_i_1223_, lean_object* v_bs_1224_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_lt(v_i_1223_, v_sz_1222_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_bs_1224_);
return v___x_1226_;
}
else
{
lean_object* v_v_1227_; lean_object* v___x_1228_; lean_object* v_bs_x27_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
v_v_1227_ = lean_array_uget(v_bs_1224_, v_i_1223_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v_bs_x27_1229_ = lean_array_uset(v_bs_1224_, v_i_1223_, v___x_1228_);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_i_1223_, v___x_1230_);
v___x_1232_ = lean_array_uset(v_bs_x27_1229_, v_i_1223_, v_v_1227_);
v_i_1223_ = v___x_1231_;
v_bs_1224_ = v___x_1232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object* v_sz_1234_, lean_object* v_i_1235_, lean_object* v_bs_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1234_);
lean_dec(v_sz_1234_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v_sz_boxed_1237_, v_i_boxed_1238_, v_bs_1236_);
return v_res_1239_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4));
v___x_1250_ = l_Lean_mkConst(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1262_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(lean_object* v_stx_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_1271_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1640_; 
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v___x_1337_, 0);
lean_dec(v_unused_1641_);
v___x_1339_ = v___x_1337_;
v_isShared_1340_ = v_isSharedCheck_1640_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v___x_1337_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1640_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
lean_inc(v_stx_1270_);
v___x_1342_ = l_Lean_Syntax_isOfKind(v_stx_1270_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_del_object(v___x_1339_);
lean_dec(v_stx_1270_);
v___x_1343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v_i_1367_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v_i_1421_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1570_; lean_object* v_args_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v_variantId_x3f_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1631_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1345_);
v___x_1632_ = l_Lean_Syntax_isNone(v___x_1631_);
if (v___x_1632_ == 0)
{
uint8_t v___x_1633_; 
lean_inc(v___x_1631_);
v___x_1633_ = l_Lean_Syntax_matchesNull(v___x_1631_, v___x_1345_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v___x_1631_);
lean_del_object(v___x_1339_);
lean_dec(v_stx_1270_);
v___x_1634_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1344_);
lean_dec(v___x_1631_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1635_);
v___x_1637_ = v___x_1339_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v_variantId_x3f_1599_ = v___x_1637_;
v___y_1600_ = v___y_1271_;
v___y_1601_ = v___y_1272_;
v___y_1602_ = v___y_1273_;
v___y_1603_ = v___y_1274_;
v___y_1604_ = v___y_1275_;
v___y_1605_ = v___y_1276_;
v___y_1606_ = v___y_1277_;
v___y_1607_ = v___y_1278_;
goto v___jp_1598_;
}
}
}
else
{
lean_object* v___x_1639_; 
lean_dec(v___x_1631_);
lean_del_object(v___x_1339_);
v___x_1639_ = lean_box(0);
v_variantId_x3f_1599_ = v___x_1639_;
v___y_1600_ = v___y_1271_;
v___y_1601_ = v___y_1272_;
v___y_1602_ = v___y_1273_;
v___y_1603_ = v___y_1274_;
v___y_1604_ = v___y_1275_;
v___y_1605_ = v___y_1276_;
v___y_1606_ = v___y_1277_;
v___y_1607_ = v___y_1278_;
goto v___jp_1598_;
}
v___jp_1346_:
{
lean_object* v_size_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_size_1368_ = lean_ctor_get(v___y_1357_, 0);
v___x_1369_ = lean_nat_add(v_size_1368_, v___x_1345_);
v___x_1370_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1357_, v___x_1369_, v_i_1367_, v___y_1349_, v___y_1358_);
lean_dec(v_i_1367_);
v___y_1281_ = v___y_1366_;
v___y_1282_ = v___y_1348_;
v___y_1283_ = v___y_1347_;
v___y_1284_ = v___y_1351_;
v___y_1285_ = v___y_1352_;
v___y_1286_ = v___y_1353_;
v___y_1287_ = v___y_1354_;
v___y_1288_ = v___y_1355_;
v___y_1289_ = v___y_1356_;
v___y_1290_ = v___y_1359_;
v___y_1291_ = v___y_1360_;
v___y_1292_ = v___y_1361_;
v___y_1293_ = v___y_1362_;
v___y_1294_ = v___y_1363_;
v___y_1295_ = v___y_1364_;
v___y_1296_ = v___y_1365_;
v___y_1297_ = v___y_1350_;
v___y_1298_ = v___x_1370_;
goto v___jp_1280_;
}
v___jp_1371_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v___y_1376_);
lean_dec_ref(v___y_1376_);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v___x_1392_, v___y_1391_);
switch(lean_obj_tag(v___x_1393_))
{
case 0:
{
lean_object* v_index_1394_; lean_object* v_size_1395_; lean_object* v___x_1396_; 
v_index_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_index_1394_);
lean_dec_ref_known(v___x_1393_, 3);
v_size_1395_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_size_1395_);
v___x_1396_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1392_, v_size_1395_, v_index_1394_, v___y_1391_, v___y_1383_);
lean_dec(v_index_1394_);
v___y_1281_ = v___y_1375_;
v___y_1282_ = v___y_1373_;
v___y_1283_ = v___y_1372_;
v___y_1284_ = v___y_1377_;
v___y_1285_ = v___y_1378_;
v___y_1286_ = v___y_1379_;
v___y_1287_ = v___y_1380_;
v___y_1288_ = v___y_1381_;
v___y_1289_ = v___y_1382_;
v___y_1290_ = v___y_1384_;
v___y_1291_ = v___y_1385_;
v___y_1292_ = v___y_1386_;
v___y_1293_ = v___y_1387_;
v___y_1294_ = v___y_1388_;
v___y_1295_ = v___y_1389_;
v___y_1296_ = v___y_1374_;
v___y_1297_ = v___y_1390_;
v___y_1298_ = v___x_1396_;
goto v___jp_1280_;
}
case 1:
{
lean_object* v_index_1397_; 
v_index_1397_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_index_1397_);
lean_dec_ref_known(v___x_1393_, 1);
v___y_1347_ = v___y_1372_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1391_;
v___y_1350_ = v___y_1390_;
v___y_1351_ = v___y_1377_;
v___y_1352_ = v___y_1378_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___y_1381_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___x_1392_;
v___y_1358_ = v___y_1383_;
v___y_1359_ = v___y_1384_;
v___y_1360_ = v___y_1385_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1387_;
v___y_1363_ = v___y_1388_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1374_;
v___y_1366_ = v___y_1375_;
v_i_1367_ = v_index_1397_;
goto v___jp_1346_;
}
default: 
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1392_, v___x_1344_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_index_1399_; 
v_index_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_index_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___y_1347_ = v___y_1372_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1391_;
v___y_1350_ = v___y_1390_;
v___y_1351_ = v___y_1377_;
v___y_1352_ = v___y_1378_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___y_1381_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___x_1392_;
v___y_1358_ = v___y_1383_;
v___y_1359_ = v___y_1384_;
v___y_1360_ = v___y_1385_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1387_;
v___y_1363_ = v___y_1388_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1374_;
v___y_1366_ = v___y_1375_;
v_i_1367_ = v_index_1399_;
goto v___jp_1346_;
}
else
{
lean_dec_ref(v___y_1391_);
lean_dec_ref(v___y_1383_);
v___y_1281_ = v___y_1375_;
v___y_1282_ = v___y_1373_;
v___y_1283_ = v___y_1372_;
v___y_1284_ = v___y_1377_;
v___y_1285_ = v___y_1378_;
v___y_1286_ = v___y_1379_;
v___y_1287_ = v___y_1380_;
v___y_1288_ = v___y_1381_;
v___y_1289_ = v___y_1382_;
v___y_1290_ = v___y_1384_;
v___y_1291_ = v___y_1385_;
v___y_1292_ = v___y_1386_;
v___y_1293_ = v___y_1387_;
v___y_1294_ = v___y_1388_;
v___y_1295_ = v___y_1389_;
v___y_1296_ = v___y_1374_;
v___y_1297_ = v___y_1390_;
v___y_1298_ = v___x_1392_;
goto v___jp_1280_;
}
}
}
}
v___jp_1400_:
{
lean_object* v_size_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_size_1422_ = lean_ctor_get(v___y_1405_, 0);
v___x_1423_ = lean_nat_add(v_size_1422_, v___x_1345_);
v___x_1424_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1405_, v___x_1423_, v_i_1421_, v___y_1403_, v___y_1412_);
lean_dec(v_i_1421_);
v___y_1281_ = v___y_1420_;
v___y_1282_ = v___y_1402_;
v___y_1283_ = v___y_1401_;
v___y_1284_ = v___y_1406_;
v___y_1285_ = v___y_1407_;
v___y_1286_ = v___y_1408_;
v___y_1287_ = v___y_1409_;
v___y_1288_ = v___y_1410_;
v___y_1289_ = v___y_1411_;
v___y_1290_ = v___y_1413_;
v___y_1291_ = v___y_1414_;
v___y_1292_ = v___y_1415_;
v___y_1293_ = v___y_1416_;
v___y_1294_ = v___y_1417_;
v___y_1295_ = v___y_1418_;
v___y_1296_ = v___y_1419_;
v___y_1297_ = v___y_1404_;
v___y_1298_ = v___x_1424_;
goto v___jp_1280_;
}
v___jp_1425_:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v___y_1445_, v___y_1444_);
switch(lean_obj_tag(v___x_1446_))
{
case 0:
{
lean_object* v_index_1447_; lean_object* v_size_1448_; lean_object* v___x_1449_; 
v_index_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_index_1447_);
lean_dec_ref_known(v___x_1446_, 3);
v_size_1448_ = lean_ctor_get(v___y_1445_, 0);
lean_inc(v_size_1448_);
v___x_1449_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1445_, v_size_1448_, v_index_1447_, v___y_1444_, v___y_1436_);
lean_dec(v_index_1447_);
v___y_1281_ = v___y_1429_;
v___y_1282_ = v___y_1427_;
v___y_1283_ = v___y_1426_;
v___y_1284_ = v___y_1430_;
v___y_1285_ = v___y_1431_;
v___y_1286_ = v___y_1432_;
v___y_1287_ = v___y_1433_;
v___y_1288_ = v___y_1434_;
v___y_1289_ = v___y_1435_;
v___y_1290_ = v___y_1437_;
v___y_1291_ = v___y_1438_;
v___y_1292_ = v___y_1439_;
v___y_1293_ = v___y_1440_;
v___y_1294_ = v___y_1441_;
v___y_1295_ = v___y_1442_;
v___y_1296_ = v___y_1428_;
v___y_1297_ = v___y_1443_;
v___y_1298_ = v___x_1449_;
goto v___jp_1280_;
}
case 1:
{
lean_object* v_index_1450_; 
v_index_1450_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_index_1450_);
lean_dec_ref_known(v___x_1446_, 1);
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1444_;
v___y_1404_ = v___y_1443_;
v___y_1405_ = v___y_1445_;
v___y_1406_ = v___y_1430_;
v___y_1407_ = v___y_1431_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1434_;
v___y_1411_ = v___y_1435_;
v___y_1412_ = v___y_1436_;
v___y_1413_ = v___y_1437_;
v___y_1414_ = v___y_1438_;
v___y_1415_ = v___y_1439_;
v___y_1416_ = v___y_1440_;
v___y_1417_ = v___y_1441_;
v___y_1418_ = v___y_1442_;
v___y_1419_ = v___y_1428_;
v___y_1420_ = v___y_1429_;
v_i_1421_ = v_index_1450_;
goto v___jp_1400_;
}
default: 
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1445_, v___x_1344_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_index_1452_; 
v_index_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_index_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1444_;
v___y_1404_ = v___y_1443_;
v___y_1405_ = v___y_1445_;
v___y_1406_ = v___y_1430_;
v___y_1407_ = v___y_1431_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1434_;
v___y_1411_ = v___y_1435_;
v___y_1412_ = v___y_1436_;
v___y_1413_ = v___y_1437_;
v___y_1414_ = v___y_1438_;
v___y_1415_ = v___y_1439_;
v___y_1416_ = v___y_1440_;
v___y_1417_ = v___y_1441_;
v___y_1418_ = v___y_1442_;
v___y_1419_ = v___y_1428_;
v___y_1420_ = v___y_1429_;
v_i_1421_ = v_index_1452_;
goto v___jp_1400_;
}
else
{
lean_dec_ref(v___y_1444_);
lean_dec_ref(v___y_1436_);
v___y_1281_ = v___y_1429_;
v___y_1282_ = v___y_1427_;
v___y_1283_ = v___y_1426_;
v___y_1284_ = v___y_1430_;
v___y_1285_ = v___y_1431_;
v___y_1286_ = v___y_1432_;
v___y_1287_ = v___y_1433_;
v___y_1288_ = v___y_1434_;
v___y_1289_ = v___y_1435_;
v___y_1290_ = v___y_1437_;
v___y_1291_ = v___y_1438_;
v___y_1292_ = v___y_1439_;
v___y_1293_ = v___y_1440_;
v___y_1294_ = v___y_1441_;
v___y_1295_ = v___y_1442_;
v___y_1296_ = v___y_1428_;
v___y_1297_ = v___y_1443_;
v___y_1298_ = v___y_1445_;
goto v___jp_1280_;
}
}
}
}
v___jp_1453_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v___y_1456_, v___y_1464_, v___y_1458_, v___y_1455_, v___y_1460_, v___y_1459_, v___y_1454_, v___y_1463_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v___x_1470_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_fst_1468_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_fst_1468_);
v_snd_1469_ = lean_ctor_get(v_a_1467_, 1);
lean_inc(v_snd_1469_);
lean_dec(v_a_1467_);
v___x_1470_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1455_, v___y_1454_, v___y_1463_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v_toGoalState_1472_; lean_object* v_mvarId_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v_toGoalState_1472_ = lean_ctor_get(v_a_1471_, 0);
lean_inc_ref(v_toGoalState_1472_);
v_mvarId_1473_ = lean_ctor_get(v_a_1471_, 1);
lean_inc_n(v_mvarId_1473_, 3);
lean_dec(v_a_1471_);
v___f_1474_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1474_, 0, v_mvarId_1473_);
lean_closure_set(v___f_1474_, 1, v_fst_1468_);
lean_closure_set(v___f_1474_, 2, v_snd_1469_);
lean_closure_set(v___f_1474_, 3, v___y_1465_);
v___x_1475_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed), 13, 3);
lean_closure_set(v___x_1475_, 0, lean_box(0));
lean_closure_set(v___x_1475_, 1, v_mvarId_1473_);
lean_closure_set(v___x_1475_, 2, v___f_1474_);
v___x_1476_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1475_, v___y_1458_, v___y_1455_, v___y_1454_, v___y_1463_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; lean_object* v___x_1480_; lean_object* v_cache_1481_; lean_object* v_symState_1482_; lean_object* v_grindState_1483_; lean_object* v_goals_1484_; lean_object* v_backwardRuleName_1485_; lean_object* v_backwardRuleSyntax_1486_; lean_object* v_simpState_1487_; lean_object* v_dsimpState_1488_; lean_object* v___x_1489_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v_fst_1478_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_fst_1478_);
v_snd_1479_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_snd_1479_);
lean_dec(v_a_1477_);
v___x_1480_ = lean_st_ref_take(v___y_1455_);
v_cache_1481_ = lean_ctor_get(v___x_1480_, 3);
lean_inc_ref(v_cache_1481_);
v_symState_1482_ = lean_ctor_get(v___x_1480_, 0);
lean_inc_ref(v_symState_1482_);
v_grindState_1483_ = lean_ctor_get(v___x_1480_, 1);
lean_inc_ref(v_grindState_1483_);
v_goals_1484_ = lean_ctor_get(v___x_1480_, 2);
lean_inc(v_goals_1484_);
lean_dec(v___x_1480_);
v_backwardRuleName_1485_ = lean_ctor_get(v_cache_1481_, 0);
lean_inc_ref(v_backwardRuleName_1485_);
v_backwardRuleSyntax_1486_ = lean_ctor_get(v_cache_1481_, 1);
lean_inc_ref(v_backwardRuleSyntax_1486_);
v_simpState_1487_ = lean_ctor_get(v_cache_1481_, 2);
lean_inc_ref(v_simpState_1487_);
v_dsimpState_1488_ = lean_ctor_get(v_cache_1481_, 3);
lean_inc_ref(v_dsimpState_1488_);
lean_dec_ref(v_cache_1481_);
v___x_1489_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_dsimpState_1488_, v___y_1457_);
switch(lean_obj_tag(v___x_1489_))
{
case 0:
{
lean_object* v_index_1490_; lean_object* v_size_1491_; lean_object* v___x_1492_; 
v_index_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_index_1490_);
lean_dec_ref_known(v___x_1489_, 3);
v_size_1491_ = lean_ctor_get(v_dsimpState_1488_, 0);
lean_inc(v_size_1491_);
v___x_1492_ = l_Std_DHashMap_Raw_setEntry___redArg(v_dsimpState_1488_, v_size_1491_, v_index_1490_, v___y_1457_, v_snd_1479_);
lean_dec(v_index_1490_);
v___y_1281_ = v_symState_1482_;
v___y_1282_ = v___y_1455_;
v___y_1283_ = v_mvarId_1473_;
v___y_1284_ = v_backwardRuleName_1485_;
v___y_1285_ = v_backwardRuleSyntax_1486_;
v___y_1286_ = v_simpState_1487_;
v___y_1287_ = v___y_1461_;
v___y_1288_ = v_grindState_1483_;
v___y_1289_ = v___y_1454_;
v___y_1290_ = v___y_1458_;
v___y_1291_ = v___y_1459_;
v___y_1292_ = v___y_1460_;
v___y_1293_ = v_fst_1478_;
v___y_1294_ = v_toGoalState_1472_;
v___y_1295_ = v___y_1462_;
v___y_1296_ = v___y_1463_;
v___y_1297_ = v_goals_1484_;
v___y_1298_ = v___x_1492_;
goto v___jp_1280_;
}
case 1:
{
lean_object* v_index_1493_; lean_object* v_size_1494_; lean_object* v_keyArray_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v_index_1493_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_index_1493_);
lean_dec_ref_known(v___x_1489_, 1);
v_size_1494_ = lean_ctor_get(v_dsimpState_1488_, 0);
v_keyArray_1495_ = lean_ctor_get(v_dsimpState_1488_, 1);
v___x_1496_ = lean_nat_add(v_size_1494_, v___x_1345_);
v___x_1497_ = lean_array_get_size(v_keyArray_1495_);
v___x_1498_ = lean_nat_dec_lt(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_dec(v___x_1496_);
lean_dec(v_index_1493_);
v___y_1372_ = v_mvarId_1473_;
v___y_1373_ = v___y_1455_;
v___y_1374_ = v___y_1463_;
v___y_1375_ = v_symState_1482_;
v___y_1376_ = v_dsimpState_1488_;
v___y_1377_ = v_backwardRuleName_1485_;
v___y_1378_ = v_backwardRuleSyntax_1486_;
v___y_1379_ = v_simpState_1487_;
v___y_1380_ = v___y_1461_;
v___y_1381_ = v_grindState_1483_;
v___y_1382_ = v___y_1454_;
v___y_1383_ = v_snd_1479_;
v___y_1384_ = v___y_1458_;
v___y_1385_ = v___y_1459_;
v___y_1386_ = v___y_1460_;
v___y_1387_ = v_fst_1478_;
v___y_1388_ = v_toGoalState_1472_;
v___y_1389_ = v___y_1462_;
v___y_1390_ = v_goals_1484_;
v___y_1391_ = v___y_1457_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1499_ = lean_unsigned_to_nat(4u);
v___x_1500_ = lean_nat_mul(v___x_1496_, v___x_1499_);
v___x_1501_ = lean_unsigned_to_nat(3u);
v___x_1502_ = lean_nat_mul(v___x_1497_, v___x_1501_);
v___x_1503_ = lean_nat_dec_le(v___x_1500_, v___x_1502_);
lean_dec(v___x_1502_);
lean_dec(v___x_1500_);
if (v___x_1503_ == 0)
{
lean_dec(v___x_1496_);
lean_dec(v_index_1493_);
v___y_1372_ = v_mvarId_1473_;
v___y_1373_ = v___y_1455_;
v___y_1374_ = v___y_1463_;
v___y_1375_ = v_symState_1482_;
v___y_1376_ = v_dsimpState_1488_;
v___y_1377_ = v_backwardRuleName_1485_;
v___y_1378_ = v_backwardRuleSyntax_1486_;
v___y_1379_ = v_simpState_1487_;
v___y_1380_ = v___y_1461_;
v___y_1381_ = v_grindState_1483_;
v___y_1382_ = v___y_1454_;
v___y_1383_ = v_snd_1479_;
v___y_1384_ = v___y_1458_;
v___y_1385_ = v___y_1459_;
v___y_1386_ = v___y_1460_;
v___y_1387_ = v_fst_1478_;
v___y_1388_ = v_toGoalState_1472_;
v___y_1389_ = v___y_1462_;
v___y_1390_ = v_goals_1484_;
v___y_1391_ = v___y_1457_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Raw_setEntry___redArg(v_dsimpState_1488_, v___x_1496_, v_index_1493_, v___y_1457_, v_snd_1479_);
lean_dec(v_index_1493_);
v___y_1281_ = v_symState_1482_;
v___y_1282_ = v___y_1455_;
v___y_1283_ = v_mvarId_1473_;
v___y_1284_ = v_backwardRuleName_1485_;
v___y_1285_ = v_backwardRuleSyntax_1486_;
v___y_1286_ = v_simpState_1487_;
v___y_1287_ = v___y_1461_;
v___y_1288_ = v_grindState_1483_;
v___y_1289_ = v___y_1454_;
v___y_1290_ = v___y_1458_;
v___y_1291_ = v___y_1459_;
v___y_1292_ = v___y_1460_;
v___y_1293_ = v_fst_1478_;
v___y_1294_ = v_toGoalState_1472_;
v___y_1295_ = v___y_1462_;
v___y_1296_ = v___y_1463_;
v___y_1297_ = v_goals_1484_;
v___y_1298_ = v___x_1504_;
goto v___jp_1280_;
}
}
}
default: 
{
lean_object* v_size_1505_; lean_object* v_keyArray_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_size_1505_ = lean_ctor_get(v_dsimpState_1488_, 0);
v_keyArray_1506_ = lean_ctor_get(v_dsimpState_1488_, 1);
v___x_1507_ = lean_nat_add(v_size_1505_, v___x_1345_);
v___x_1508_ = lean_array_get_size(v_keyArray_1506_);
v___x_1509_ = lean_nat_dec_lt(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec(v___x_1507_);
v___x_1510_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_dsimpState_1488_);
lean_dec_ref(v_dsimpState_1488_);
v___y_1426_ = v_mvarId_1473_;
v___y_1427_ = v___y_1455_;
v___y_1428_ = v___y_1463_;
v___y_1429_ = v_symState_1482_;
v___y_1430_ = v_backwardRuleName_1485_;
v___y_1431_ = v_backwardRuleSyntax_1486_;
v___y_1432_ = v_simpState_1487_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v_grindState_1483_;
v___y_1435_ = v___y_1454_;
v___y_1436_ = v_snd_1479_;
v___y_1437_ = v___y_1458_;
v___y_1438_ = v___y_1459_;
v___y_1439_ = v___y_1460_;
v___y_1440_ = v_fst_1478_;
v___y_1441_ = v_toGoalState_1472_;
v___y_1442_ = v___y_1462_;
v___y_1443_ = v_goals_1484_;
v___y_1444_ = v___y_1457_;
v___y_1445_ = v___x_1510_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1511_ = lean_unsigned_to_nat(4u);
v___x_1512_ = lean_nat_mul(v___x_1507_, v___x_1511_);
lean_dec(v___x_1507_);
v___x_1513_ = lean_unsigned_to_nat(3u);
v___x_1514_ = lean_nat_mul(v___x_1508_, v___x_1513_);
v___x_1515_ = lean_nat_dec_le(v___x_1512_, v___x_1514_);
lean_dec(v___x_1514_);
lean_dec(v___x_1512_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_dsimpState_1488_);
lean_dec_ref(v_dsimpState_1488_);
v___y_1426_ = v_mvarId_1473_;
v___y_1427_ = v___y_1455_;
v___y_1428_ = v___y_1463_;
v___y_1429_ = v_symState_1482_;
v___y_1430_ = v_backwardRuleName_1485_;
v___y_1431_ = v_backwardRuleSyntax_1486_;
v___y_1432_ = v_simpState_1487_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v_grindState_1483_;
v___y_1435_ = v___y_1454_;
v___y_1436_ = v_snd_1479_;
v___y_1437_ = v___y_1458_;
v___y_1438_ = v___y_1459_;
v___y_1439_ = v___y_1460_;
v___y_1440_ = v_fst_1478_;
v___y_1441_ = v_toGoalState_1472_;
v___y_1442_ = v___y_1462_;
v___y_1443_ = v_goals_1484_;
v___y_1444_ = v___y_1457_;
v___y_1445_ = v___x_1516_;
goto v___jp_1425_;
}
else
{
v___y_1426_ = v_mvarId_1473_;
v___y_1427_ = v___y_1455_;
v___y_1428_ = v___y_1463_;
v___y_1429_ = v_symState_1482_;
v___y_1430_ = v_backwardRuleName_1485_;
v___y_1431_ = v_backwardRuleSyntax_1486_;
v___y_1432_ = v_simpState_1487_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v_grindState_1483_;
v___y_1435_ = v___y_1454_;
v___y_1436_ = v_snd_1479_;
v___y_1437_ = v___y_1458_;
v___y_1438_ = v___y_1459_;
v___y_1439_ = v___y_1460_;
v___y_1440_ = v_fst_1478_;
v___y_1441_ = v_toGoalState_1472_;
v___y_1442_ = v___y_1462_;
v___y_1443_ = v_goals_1484_;
v___y_1444_ = v___y_1457_;
v___y_1445_ = v_dsimpState_1488_;
goto v___jp_1425_;
}
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_mvarId_1473_);
lean_dec_ref(v_toGoalState_1472_);
lean_dec_ref(v___y_1457_);
v_a_1517_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1476_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1476_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_snd_1469_);
lean_dec(v_fst_1468_);
lean_dec_ref(v___y_1465_);
lean_dec_ref(v___y_1457_);
v_a_1525_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1470_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1470_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___y_1465_);
lean_dec_ref(v___y_1457_);
v_a_1533_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1466_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1466_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
v___jp_1541_:
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v___y_1550_, v___y_1544_, v___y_1543_, v___y_1546_, v___y_1545_, v___y_1542_, v___y_1549_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v_cache_1555_; lean_object* v_dsimpState_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc_n(v_a_1553_, 2);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = lean_st_ref_get(v___y_1543_);
v_cache_1555_ = lean_ctor_get(v___x_1554_, 3);
lean_inc_ref(v_cache_1555_);
lean_dec(v___x_1554_);
v_dsimpState_1556_ = lean_ctor_get(v_cache_1555_, 3);
lean_inc_ref(v_dsimpState_1556_);
lean_dec_ref(v_cache_1555_);
lean_inc(v___y_1551_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___y_1551_);
lean_ctor_set(v___x_1557_, 1, v_a_1553_);
v___x_1558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg(v_dsimpState_1556_, v___x_1557_);
lean_dec_ref(v_dsimpState_1556_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14);
v___y_1454_ = v___y_1542_;
v___y_1455_ = v___y_1543_;
v___y_1456_ = v___y_1551_;
v___y_1457_ = v___x_1557_;
v___y_1458_ = v___y_1544_;
v___y_1459_ = v___y_1545_;
v___y_1460_ = v___y_1546_;
v___y_1461_ = v___y_1547_;
v___y_1462_ = v___y_1548_;
v___y_1463_ = v___y_1549_;
v___y_1464_ = v_a_1553_;
v___y_1465_ = v___x_1559_;
goto v___jp_1453_;
}
else
{
lean_object* v_val_1560_; 
v_val_1560_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v___x_1558_, 1);
v___y_1454_ = v___y_1542_;
v___y_1455_ = v___y_1543_;
v___y_1456_ = v___y_1551_;
v___y_1457_ = v___x_1557_;
v___y_1458_ = v___y_1544_;
v___y_1459_ = v___y_1545_;
v___y_1460_ = v___y_1546_;
v___y_1461_ = v___y_1547_;
v___y_1462_ = v___y_1548_;
v___y_1463_ = v___y_1549_;
v___y_1464_ = v_a_1553_;
v___y_1465_ = v_val_1560_;
goto v___jp_1453_;
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v___y_1551_);
v_a_1561_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1552_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1552_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
v___jp_1569_:
{
if (lean_obj_tag(v___y_1570_) == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_box(0);
v___y_1542_ = v___y_1576_;
v___y_1543_ = v___y_1573_;
v___y_1544_ = v___y_1572_;
v___y_1545_ = v___y_1575_;
v___y_1546_ = v___y_1574_;
v___y_1547_ = v___y_1578_;
v___y_1548_ = v___y_1579_;
v___y_1549_ = v___y_1577_;
v___y_1550_ = v_args_1571_;
v___y_1551_ = v___x_1580_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1581_; lean_object* v___x_1582_; 
v_val_1581_ = lean_ctor_get(v___y_1570_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v___y_1570_, 1);
v___x_1582_ = l_Lean_TSyntax_getId(v_val_1581_);
lean_dec(v_val_1581_);
v___y_1542_ = v___y_1576_;
v___y_1543_ = v___y_1573_;
v___y_1544_ = v___y_1572_;
v___y_1545_ = v___y_1575_;
v___y_1546_ = v___y_1574_;
v___y_1547_ = v___y_1578_;
v___y_1548_ = v___y_1579_;
v___y_1549_ = v___y_1577_;
v___y_1550_ = v_args_1571_;
v___y_1551_ = v___x_1582_;
goto v___jp_1541_;
}
}
v___jp_1583_:
{
size_t v_sz_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v_sz_1594_ = lean_array_size(v___y_1593_);
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v_sz_1594_, v___x_1595_, v___y_1593_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
lean_dec(v___y_1585_);
v___x_1597_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1597_;
}
else
{
v___y_1570_ = v___y_1585_;
v_args_1571_ = v___x_1596_;
v___y_1572_ = v___y_1592_;
v___y_1573_ = v___y_1588_;
v___y_1574_ = v___y_1589_;
v___y_1575_ = v___y_1590_;
v___y_1576_ = v___y_1586_;
v___y_1577_ = v___y_1591_;
v___y_1578_ = v___y_1587_;
v___y_1579_ = v___y_1584_;
goto v___jp_1569_;
}
}
v___jp_1598_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_unsigned_to_nat(2u);
v___x_1609_ = l_Lean_Syntax_getArg(v_stx_1270_, v___x_1608_);
lean_dec(v_stx_1270_);
v___x_1610_ = l_Lean_Syntax_isNone(v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1609_);
v___x_1612_ = l_Lean_Syntax_matchesNull(v___x_1609_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec(v___x_1609_);
lean_dec(v_variantId_x3f_1599_);
v___x_1613_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1614_ = l_Lean_Syntax_getArg(v___x_1609_, v___x_1345_);
lean_dec(v___x_1609_);
v___x_1615_ = l_Lean_Syntax_getArgs(v___x_1614_);
lean_dec(v___x_1614_);
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15));
v___x_1617_ = lean_array_get_size(v___x_1615_);
v___x_1618_ = lean_nat_dec_lt(v___x_1344_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_dec_ref(v___x_1615_);
v___y_1584_ = v___y_1607_;
v___y_1585_ = v_variantId_x3f_1599_;
v___y_1586_ = v___y_1604_;
v___y_1587_ = v___y_1606_;
v___y_1588_ = v___y_1601_;
v___y_1589_ = v___y_1602_;
v___y_1590_ = v___y_1603_;
v___y_1591_ = v___y_1605_;
v___y_1592_ = v___y_1600_;
v___y_1593_ = v___x_1616_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_box(v___x_1612_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v___x_1616_);
v___x_1621_ = lean_nat_dec_le(v___x_1617_, v___x_1617_);
if (v___x_1621_ == 0)
{
if (v___x_1618_ == 0)
{
lean_dec_ref_known(v___x_1620_, 2);
lean_dec_ref(v___x_1615_);
v___y_1584_ = v___y_1607_;
v___y_1585_ = v_variantId_x3f_1599_;
v___y_1586_ = v___y_1604_;
v___y_1587_ = v___y_1606_;
v___y_1588_ = v___y_1601_;
v___y_1589_ = v___y_1602_;
v___y_1590_ = v___y_1603_;
v___y_1591_ = v___y_1605_;
v___y_1592_ = v___y_1600_;
v___y_1593_ = v___x_1616_;
goto v___jp_1583_;
}
else
{
size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; lean_object* v_snd_1625_; 
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = lean_usize_of_nat(v___x_1617_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7(v___x_1612_, v___x_1610_, v___x_1615_, v___x_1622_, v___x_1623_, v___x_1620_);
lean_dec_ref(v___x_1615_);
v_snd_1625_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_snd_1625_);
lean_dec_ref(v___x_1624_);
v___y_1584_ = v___y_1607_;
v___y_1585_ = v_variantId_x3f_1599_;
v___y_1586_ = v___y_1604_;
v___y_1587_ = v___y_1606_;
v___y_1588_ = v___y_1601_;
v___y_1589_ = v___y_1602_;
v___y_1590_ = v___y_1603_;
v___y_1591_ = v___y_1605_;
v___y_1592_ = v___y_1600_;
v___y_1593_ = v_snd_1625_;
goto v___jp_1583_;
}
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; lean_object* v_snd_1629_; 
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1617_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__7(v___x_1612_, v___x_1610_, v___x_1615_, v___x_1626_, v___x_1627_, v___x_1620_);
lean_dec_ref(v___x_1615_);
v_snd_1629_ = lean_ctor_get(v___x_1628_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1628_);
v___y_1584_ = v___y_1607_;
v___y_1585_ = v_variantId_x3f_1599_;
v___y_1586_ = v___y_1604_;
v___y_1587_ = v___y_1606_;
v___y_1588_ = v___y_1601_;
v___y_1589_ = v___y_1602_;
v___y_1590_ = v___y_1603_;
v___y_1591_ = v___y_1605_;
v___y_1592_ = v___y_1600_;
v___y_1593_ = v_snd_1629_;
goto v___jp_1583_;
}
}
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v___x_1609_);
v___x_1630_ = lean_box(0);
v___y_1570_ = v_variantId_x3f_1599_;
v_args_1571_ = v___x_1630_;
v___y_1572_ = v___y_1600_;
v___y_1573_ = v___y_1601_;
v___y_1574_ = v___y_1602_;
v___y_1575_ = v___y_1603_;
v___y_1576_ = v___y_1604_;
v___y_1577_ = v___y_1605_;
v___y_1578_ = v___y_1606_;
v___y_1579_ = v___y_1607_;
goto v___jp_1569_;
}
}
}
}
}
else
{
lean_dec(v_stx_1270_);
return v___x_1337_;
}
v___jp_1280_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1299_, 0, v___y_1284_);
lean_ctor_set(v___x_1299_, 1, v___y_1285_);
lean_ctor_set(v___x_1299_, 2, v___y_1286_);
lean_ctor_set(v___x_1299_, 3, v___y_1298_);
v___x_1300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1300_, 0, v___y_1281_);
lean_ctor_set(v___x_1300_, 1, v___y_1288_);
lean_ctor_set(v___x_1300_, 2, v___y_1297_);
lean_ctor_set(v___x_1300_, 3, v___x_1299_);
v___x_1301_ = lean_st_ref_put(v___y_1282_, v___x_1300_);
if (lean_obj_tag(v___y_1293_) == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref_known(v___y_1293_, 0);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1283_);
v___x_1302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1);
v___x_1303_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_1302_, v___y_1289_, v___y_1296_, v___y_1287_, v___y_1295_);
return v___x_1303_;
}
else
{
lean_object* v_e_x27_1304_; uint8_t v___x_1305_; 
v_e_x27_1304_ = lean_ctor_get(v___y_1293_, 0);
lean_inc_ref_n(v_e_x27_1304_, 2);
lean_dec_ref_known(v___y_1293_, 1);
v___x_1305_ = l_Lean_Expr_isTrue(v_e_x27_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_inc(v___y_1283_);
v___x_1306_ = l_Lean_MVarId_getDecl(v___y_1283_, v___y_1289_, v___y_1296_, v___y_1287_, v___y_1295_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v_userName_1308_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v_userName_1308_ = lean_ctor_get(v_a_1307_, 0);
lean_inc(v_userName_1308_);
lean_dec(v_a_1307_);
v___x_1309_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_1304_, v_userName_1308_, v___y_1289_, v___y_1296_, v___y_1287_, v___y_1295_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc_n(v_a_1310_, 2);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v___y_1283_, v_a_1310_, v___y_1296_);
lean_dec_ref(v___x_1311_);
v___x_1312_ = l_Lean_Expr_mvarId_x21(v_a_1310_);
lean_dec(v_a_1310_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___y_1294_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1315_, v___y_1282_, v___y_1289_, v___y_1296_, v___y_1287_, v___y_1295_);
return v___x_1316_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1283_);
v_a_1317_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1309_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1309_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_e_x27_1304_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1283_);
v_a_1325_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1306_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1306_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v_e_x27_1304_);
lean_dec_ref(v___y_1294_);
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5);
v___x_1335_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v___y_1283_, v___x_1334_, v___y_1296_);
lean_dec_ref(v___x_1335_);
v___x_1336_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1333_, v___y_1282_, v___y_1289_, v___y_1296_, v___y_1287_, v___y_1295_);
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed(lean_object* v_stx_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(v_stx_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(lean_object* v_stx_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___f_1663_; lean_object* v___x_1664_; 
v___f_1663_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1663_, 0, v_stx_1653_);
v___x_1664_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1663_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed(lean_object* v_stx_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(v_stx_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object* v_mvarId_1676_, lean_object* v_val_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_mvarId_1676_, v_val_1677_, v___y_1683_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___boxed(lean_object* v_mvarId_1688_, lean_object* v_val_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(v_mvarId_1688_, v_val_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object* v_00_u03b2_1700_, lean_object* v_m_1701_, lean_object* v_query_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_m_1701_, v_query_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object* v_00_u03b2_1704_, lean_object* v_m_1705_, lean_object* v_query_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(v_00_u03b2_1704_, v_m_1705_, v_query_1706_);
lean_dec_ref(v_query_1706_);
lean_dec_ref(v_m_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object* v_00_u03b2_1708_, lean_object* v_m_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object* v_00_u03b2_1711_, lean_object* v_m_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(v_00_u03b2_1711_, v_m_1712_);
lean_dec_ref(v_m_1712_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(lean_object* v_00_u03b2_1714_, lean_object* v_m_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___redArg(v_m_1715_, v_a_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object* v_00_u03b2_1718_, lean_object* v_m_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_00_u03b2_1718_, v_m_1719_, v_a_1720_);
lean_dec_ref(v_a_1720_);
lean_dec_ref(v_m_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object* v_00_u03b2_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_x_1723_, v_x_1724_, v_x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4(lean_object* v_00_u03b2_1727_, lean_object* v_m_1728_, lean_object* v_query_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___redArg(v_m_1728_, v_query_1729_, v_x_1730_, v_x_1731_, v_x_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1735_, lean_object* v_m_1736_, lean_object* v_query_1737_, lean_object* v_x_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__4(v_00_u03b2_1735_, v_m_1736_, v_query_1737_, v_x_1738_, v_x_1739_, v_x_1740_, v_x_1741_);
lean_dec_ref(v_query_1737_);
lean_dec_ref(v_m_1736_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6(lean_object* v_00_u03b2_1743_, lean_object* v_init_1744_, lean_object* v_b_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___redArg(v_init_1744_, v_b_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1747_, lean_object* v_init_1748_, lean_object* v_b_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6(v_00_u03b2_1747_, v_init_1748_, v_b_1749_);
lean_dec_ref(v_b_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8(lean_object* v_00_u03b2_1751_, lean_object* v_m_1752_, lean_object* v_query_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___redArg(v_m_1752_, v_query_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_query_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5_spec__8(v_00_u03b2_1755_, v_m_1756_, v_query_1757_);
lean_dec_ref(v_query_1757_);
lean_dec_ref(v_m_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_1759_, lean_object* v_x_1760_, size_t v_x_1761_, size_t v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___redArg(v_x_1760_, v_x_1761_, v_x_1762_, v_x_1763_, v_x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
size_t v_x_14653__boxed_1772_; size_t v_x_14654__boxed_1773_; lean_object* v_res_1774_; 
v_x_14653__boxed_1772_ = lean_unbox_usize(v_x_1768_);
lean_dec(v_x_1768_);
v_x_14654__boxed_1773_ = lean_unbox_usize(v_x_1769_);
lean_dec(v_x_1769_);
v_res_1774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3(v_00_u03b2_1766_, v_x_1767_, v_x_14653__boxed_1772_, v_x_14654__boxed_1773_, v_x_1770_, v_x_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_1775_, lean_object* v_b_1776_, lean_object* v_acc_1777_, lean_object* v_i_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___redArg(v_b_1776_, v_acc_1777_, v_i_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_b_1781_, lean_object* v_acc_1782_, lean_object* v_i_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__6_spec__8(v_00_u03b2_1780_, v_b_1781_, v_acc_1782_, v_i_1783_);
lean_dec_ref(v_b_1781_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1785_, lean_object* v_n_1786_, lean_object* v_k_1787_, lean_object* v_v_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9___redArg(v_n_1786_, v_k_1787_, v_v_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10(lean_object* v_00_u03b2_1790_, size_t v_depth_1791_, lean_object* v_keys_1792_, lean_object* v_vals_1793_, lean_object* v_heq_1794_, lean_object* v_i_1795_, lean_object* v_entries_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___redArg(v_depth_1791_, v_keys_1792_, v_vals_1793_, v_i_1795_, v_entries_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1798_, lean_object* v_depth_1799_, lean_object* v_keys_1800_, lean_object* v_vals_1801_, lean_object* v_heq_1802_, lean_object* v_i_1803_, lean_object* v_entries_1804_){
_start:
{
size_t v_depth_boxed_1805_; lean_object* v_res_1806_; 
v_depth_boxed_1805_ = lean_unbox_usize(v_depth_1799_);
lean_dec(v_depth_1799_);
v_res_1806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__10(v_00_u03b2_1798_, v_depth_boxed_1805_, v_keys_1800_, v_vals_1801_, v_heq_1802_, v_i_1803_, v_entries_1804_);
lean_dec_ref(v_vals_1801_);
lean_dec_ref(v_keys_1800_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2_spec__3_spec__9_spec__13___redArg(v_x_1808_, v_x_1809_, v_x_1810_, v_x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1(){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1854_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15));
v___x_1857_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed), 10, 0);
v___x_1858_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1854_, v___x_1855_, v___x_1856_, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___boxed(lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
return v_res_1860_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_DSimp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_DSimp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_DSimp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_DSimp(builtin);
}
#ifdef __cplusplus
}
#endif
