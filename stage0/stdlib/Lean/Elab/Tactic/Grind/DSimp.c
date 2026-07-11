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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint64_t l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_ofArray(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_188_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_188_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_188_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_188_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; 
v_fst_166_ = lean_ctor_get(v_a_162_, 0);
lean_inc(v_fst_166_);
v_snd_167_ = lean_ctor_get(v_a_162_, 1);
lean_inc(v_snd_167_);
lean_dec(v_a_162_);
v___x_174_ = lean_array_get_size(v_fst_166_);
v___x_175_ = lean_nat_dec_eq(v___x_174_, v___x_157_);
v___x_176_ = lean_bool_not(v___x_175_);
if (v___x_176_ == 0)
{
goto v___jp_168_;
}
else
{
uint8_t v___x_177_; 
v___x_177_ = lean_unbox(v_snd_167_);
if (v___x_177_ == 0)
{
goto v___jp_168_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_snd_167_);
lean_dec(v_fst_166_);
lean_del_object(v___x_164_);
v___x_178_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3);
v___x_179_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_178_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
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
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_161_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_161_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4));
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___boxed(lean_object* v_args_x3f_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v_args_x3f_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_args_x3f_199_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object* v_00_u03b1_210_, lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v_msg_211_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object* v_00_u03b1_222_, lean_object* v_msg_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(v_00_u03b1_222_, v_msg_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(lean_object* v_fvarIds_234_, lean_object* v_x_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = l_Lean_FVarIdSet_ofArray(v_fvarIds_234_);
v___x_248_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v___x_247_, v___y_236_, v___y_242_, v___y_244_, v___y_245_);
lean_dec(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0___boxed(lean_object* v_fvarIds_249_, lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(v_fvarIds_249_, v_x_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v_fvarIds_249_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1(lean_object* v_pre_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc_ref(v___y_270_);
lean_inc_ref(v___y_264_);
v___x_275_ = lean_apply_11(v_pre_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
if (lean_obj_tag(v_a_276_) == 0)
{
uint8_t v_done_277_; 
v_done_277_ = lean_ctor_get_uint8(v_a_276_, 0);
lean_dec_ref_known(v_a_276_, 0);
if (v_done_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref_known(v___x_275_, 1);
v___x_278_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_264_, v___y_270_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_270_);
return v___x_278_;
}
else
{
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_270_);
lean_dec_ref(v___y_264_);
return v___x_275_;
}
}
else
{
uint8_t v_done_279_; 
lean_dec_ref(v___y_264_);
v_done_279_ = lean_ctor_get_uint8(v_a_276_, sizeof(void*)*1);
if (v_done_279_ == 0)
{
lean_object* v_e_x27_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref_known(v___x_275_, 1);
v_e_x27_280_ = lean_ctor_get(v_a_276_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_276_);
if (v_isSharedCheck_298_ == 0)
{
v___x_282_ = v_a_276_;
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_e_x27_280_);
lean_dec(v_a_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; 
lean_inc_ref(v_e_x27_280_);
v___x_284_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_280_, v___y_270_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_270_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
if (lean_obj_tag(v_a_285_) == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_284_, 0);
lean_dec(v_unused_297_);
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_296_;
goto v_resetjp_286_;
}
else
{
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_296_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v_done_289_; lean_object* v___x_291_; 
v_done_289_ = lean_ctor_get_uint8(v_a_285_, 0);
lean_dec_ref_known(v_a_285_, 0);
if (v_isShared_283_ == 0)
{
v___x_291_ = v___x_282_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_e_x27_280_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v_done_289_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_291_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_285_, 1);
lean_del_object(v___x_282_);
lean_dec_ref(v_e_x27_280_);
return v___x_284_;
}
}
else
{
lean_del_object(v___x_282_);
lean_dec_ref(v_e_x27_280_);
return v___x_284_;
}
}
}
else
{
lean_dec_ref_known(v_a_276_, 1);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_270_);
return v___x_275_;
}
}
}
else
{
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_270_);
lean_dec_ref(v___y_264_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1___boxed(lean_object* v_pre_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1(v_pre_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(lean_object* v_pre_312_, lean_object* v_args_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_fvarIds_325_; uint8_t v_zetaDeltaAll_326_; lean_object* v_pre_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; 
v_fvarIds_325_ = lean_ctor_get(v_args_313_, 0);
v_zetaDeltaAll_326_ = lean_ctor_get_uint8(v_args_313_, sizeof(void*)*1);
if (v_zetaDeltaAll_326_ == 0)
{
v_pre_328_ = v_pre_312_;
v___y_329_ = v_a_314_;
v___y_330_ = v_a_315_;
v___y_331_ = v_a_316_;
v___y_332_ = v_a_317_;
v___y_333_ = v_a_318_;
v___y_334_ = v_a_319_;
v___y_335_ = v_a_320_;
v___y_336_ = v_a_321_;
v___y_337_ = v_a_322_;
v___y_338_ = v_a_323_;
goto v___jp_327_;
}
else
{
lean_object* v_pre_368_; 
v_pre_368_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__1___boxed), 12, 1);
lean_closure_set(v_pre_368_, 0, v_pre_312_);
v_pre_328_ = v_pre_368_;
v___y_329_ = v_a_314_;
v___y_330_ = v_a_315_;
v___y_331_ = v_a_316_;
v___y_332_ = v_a_317_;
v___y_333_ = v_a_318_;
v___y_334_ = v_a_319_;
v___y_335_ = v_a_320_;
v___y_336_ = v_a_321_;
v___y_337_ = v_a_322_;
v___y_338_ = v_a_323_;
goto v___jp_327_;
}
v___jp_327_:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_array_get_size(v_fvarIds_325_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_nat_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
lean_inc(v___y_332_);
lean_inc(v___y_331_);
lean_inc(v___y_330_);
lean_inc_ref(v___y_329_);
v___x_342_ = lean_apply_11(v_pre_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, lean_box(0));
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
v___x_344_ = lean_box(0);
if (lean_obj_tag(v_a_343_) == 0)
{
uint8_t v_done_345_; 
v_done_345_ = lean_ctor_get_uint8(v_a_343_, 0);
lean_dec_ref_known(v_a_343_, 0);
if (v_done_345_ == 0)
{
lean_object* v___x_346_; 
lean_dec_ref_known(v___x_342_, 1);
v___x_346_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(v_fvarIds_325_, v___x_344_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_346_;
}
else
{
lean_dec_ref(v___y_329_);
return v___x_342_;
}
}
else
{
uint8_t v_done_347_; 
lean_dec_ref(v___y_329_);
v_done_347_ = lean_ctor_get_uint8(v_a_343_, sizeof(void*)*1);
if (v_done_347_ == 0)
{
lean_object* v_e_x27_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref_known(v___x_342_, 1);
v_e_x27_348_ = lean_ctor_get(v_a_343_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_a_343_);
if (v_isSharedCheck_366_ == 0)
{
v___x_350_ = v_a_343_;
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_e_x27_348_);
lean_dec(v_a_343_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; 
lean_inc_ref(v_e_x27_348_);
v___x_352_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___lam__0(v_fvarIds_325_, v___x_344_, v_e_x27_348_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
if (lean_obj_tag(v_a_353_) == 0)
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_364_; 
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_352_, 0);
lean_dec(v_unused_365_);
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
else
{
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v_done_357_; lean_object* v___x_359_; 
v_done_357_ = lean_ctor_get_uint8(v_a_353_, 0);
lean_dec_ref_known(v_a_353_, 0);
if (v_isShared_351_ == 0)
{
v___x_359_ = v___x_350_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_e_x27_348_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v_done_357_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_359_);
v___x_361_ = v___x_355_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
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
lean_dec_ref_known(v_a_353_, 1);
lean_del_object(v___x_350_);
lean_dec_ref(v_e_x27_348_);
return v___x_352_;
}
}
else
{
lean_del_object(v___x_350_);
lean_dec_ref(v_e_x27_348_);
return v___x_352_;
}
}
}
else
{
lean_dec_ref_known(v_a_343_, 1);
return v___x_342_;
}
}
}
else
{
lean_dec_ref(v___y_329_);
return v___x_342_;
}
}
else
{
lean_object* v___x_367_; 
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
lean_inc(v___y_332_);
lean_inc(v___y_331_);
lean_inc(v___y_330_);
v___x_367_ = lean_apply_11(v_pre_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, lean_box(0));
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed(lean_object* v_pre_369_, lean_object* v_args_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(v_pre_369_, v_args_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_args_370_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
lean_inc_ref(v___y_384_);
v___x_395_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
if (lean_obj_tag(v_a_396_) == 0)
{
uint8_t v_done_397_; 
v_done_397_ = lean_ctor_get_uint8(v_a_396_, 0);
lean_dec_ref_known(v_a_396_, 0);
if (v_done_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec_ref_known(v___x_395_, 1);
v___x_398_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_384_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec_ref(v___y_384_);
return v___x_398_;
}
else
{
lean_dec_ref(v___y_384_);
return v___x_395_;
}
}
else
{
uint8_t v_done_399_; 
lean_dec_ref(v___y_384_);
v_done_399_ = lean_ctor_get_uint8(v_a_396_, sizeof(void*)*1);
if (v_done_399_ == 0)
{
lean_object* v_e_x27_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref_known(v___x_395_, 1);
v_e_x27_400_ = lean_ctor_get(v_a_396_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_a_396_);
if (v_isSharedCheck_418_ == 0)
{
v___x_402_ = v_a_396_;
v_isShared_403_ = v_isSharedCheck_418_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_e_x27_400_);
lean_dec(v_a_396_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_418_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_400_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
if (lean_obj_tag(v_a_405_) == 0)
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_416_; 
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_404_, 0);
lean_dec(v_unused_417_);
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_416_;
goto v_resetjp_406_;
}
else
{
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_416_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint8_t v_done_409_; lean_object* v___x_411_; 
v_done_409_ = lean_ctor_get_uint8(v_a_405_, 0);
lean_dec_ref_known(v_a_405_, 0);
if (v_isShared_403_ == 0)
{
v___x_411_ = v___x_402_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_e_x27_400_);
v___x_411_ = v_reuseFailAlloc_415_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v_done_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_411_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_405_, 1);
lean_del_object(v___x_402_);
lean_dec_ref(v_e_x27_400_);
return v___x_404_;
}
}
else
{
lean_del_object(v___x_402_);
lean_dec_ref(v_e_x27_400_);
return v___x_404_;
}
}
}
else
{
lean_dec_ref_known(v_a_396_, 1);
return v___x_395_;
}
}
}
else
{
lean_dec_ref(v___y_384_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0___boxed(lean_object* v_x_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(v_x_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(lean_object* v___f_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
lean_inc_ref(v___y_433_);
v___x_444_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_433_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
v___x_446_ = lean_box(0);
if (lean_obj_tag(v_a_445_) == 0)
{
uint8_t v_done_447_; 
v_done_447_ = lean_ctor_get_uint8(v_a_445_, 0);
lean_dec_ref_known(v_a_445_, 0);
if (v_done_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec_ref_known(v___x_444_, 1);
v___x_448_ = lean_apply_12(v___f_432_, v___x_446_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, lean_box(0));
return v___x_448_;
}
else
{
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v___f_432_);
return v___x_444_;
}
}
else
{
uint8_t v_done_449_; 
lean_dec_ref(v___y_433_);
v_done_449_ = lean_ctor_get_uint8(v_a_445_, sizeof(void*)*1);
if (v_done_449_ == 0)
{
lean_object* v_e_x27_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref_known(v___x_444_, 1);
v_e_x27_450_ = lean_ctor_get(v_a_445_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_468_ == 0)
{
v___x_452_ = v_a_445_;
v_isShared_453_ = v_isSharedCheck_468_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_e_x27_450_);
lean_dec(v_a_445_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_468_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; 
lean_inc_ref(v_e_x27_450_);
v___x_454_ = lean_apply_12(v___f_432_, v___x_446_, v_e_x27_450_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, lean_box(0));
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
if (lean_obj_tag(v_a_455_) == 0)
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_466_; 
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_467_);
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
else
{
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint8_t v_done_459_; lean_object* v___x_461_; 
v_done_459_ = lean_ctor_get_uint8(v_a_455_, 0);
lean_dec_ref_known(v_a_455_, 0);
if (v_isShared_453_ == 0)
{
v___x_461_ = v___x_452_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_e_x27_450_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*1, v_done_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_461_);
v___x_463_ = v___x_457_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_455_, 1);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_x27_450_);
return v___x_454_;
}
}
else
{
lean_del_object(v___x_452_);
lean_dec_ref(v_e_x27_450_);
return v___x_454_;
}
}
}
else
{
lean_dec_ref_known(v_a_445_, 1);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___f_432_);
return v___x_444_;
}
}
}
else
{
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v___f_432_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1___boxed(lean_object* v___f_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(v___f_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(lean_object* v_args_487_){
_start:
{
lean_object* v_pre_489_; lean_object* v_pre_490_; lean_object* v_post_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_pre_489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1));
v_pre_490_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed), 13, 2);
lean_closure_set(v_pre_490_, 0, v_pre_489_);
lean_closure_set(v_pre_490_, 1, v_args_487_);
v_post_491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2));
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_pre_490_);
lean_ctor_set(v___x_492_, 1, v_post_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___boxed(lean_object* v_args_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(lean_object* v_args_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_497_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___boxed(lean_object* v_args_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(v_args_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg(){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0));
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___boxed(lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(lean_object* v_x_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed(lean_object* v_x_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(v_x_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_x_538_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(lean_object* v_stx_x3f_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
if (lean_obj_tag(v_stx_x3f_550_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_561_; 
v_val_560_ = lean_ctor_get(v_stx_x3f_550_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v_stx_x3f_550_, 1);
v___x_561_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(v_val_560_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_stx_x3f_550_);
v___x_562_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed), 11, 0);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc___boxed(lean_object* v_stx_x3f_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_stx_x3f_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_574_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(lean_object* v_variantName_578_, lean_object* v_args_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = l_Lean_Name_isAnonymous(v_variantName_578_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v_env_591_; lean_object* v___x_592_; 
v___x_590_ = lean_st_ref_get(v_a_587_);
v_env_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc_ref(v_env_591_);
lean_dec(v___x_590_);
v___x_592_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_591_, v_variantName_578_);
if (lean_obj_tag(v___x_592_) == 1)
{
lean_object* v_val_593_; lean_object* v_pre_x3f_594_; lean_object* v_post_x3f_595_; lean_object* v_config_596_; lean_object* v___x_597_; 
lean_dec(v_variantName_578_);
v_val_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_592_, 1);
v_pre_x3f_594_ = lean_ctor_get(v_val_593_, 0);
lean_inc(v_pre_x3f_594_);
v_post_x3f_595_ = lean_ctor_get(v_val_593_, 1);
lean_inc(v_post_x3f_595_);
v_config_596_ = lean_ctor_get(v_val_593_, 2);
lean_inc(v_config_596_);
lean_dec(v_val_593_);
v___x_597_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_pre_x3f_594_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_post_x3f_595_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_610_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_610_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_604_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed), 13, 2);
lean_closure_set(v___x_604_, 0, v_a_598_);
lean_closure_set(v___x_604_, 1, v_args_579_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_a_600_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v_config_596_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_606_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_598_);
lean_dec(v_config_596_);
lean_dec_ref(v_args_579_);
v_a_611_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_599_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_599_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_config_596_);
lean_dec(v_post_x3f_595_);
lean_dec_ref(v_args_579_);
v_a_619_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_597_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_597_);
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
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v___x_592_);
lean_dec_ref(v_args_579_);
v___x_627_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1);
v___x_628_ = l_Lean_MessageData_ofName(v_variantName_578_);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_631_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_632_;
}
}
else
{
lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_variantName_578_);
v___x_633_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_579_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = lean_unsigned_to_nat(100000u);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_a_634_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_639_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___boxed(lean_object* v_variantName_644_, lean_object* v_args_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v_variantName_644_, v_args_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_655_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg(){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___boxed(lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(lean_object* v_00_u03b1_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(v_00_u03b1_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
v___x_697_ = lean_apply_10(v_x_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, lean_box(0));
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed(lean_object* v_x_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(v_x_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(lean_object* v_mvarId_710_, lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___f_722_; lean_object* v___x_723_; 
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
v___f_722_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_722_, 0, v_x_711_);
lean_closure_set(v___f_722_, 1, v___y_712_);
lean_closure_set(v___f_722_, 2, v___y_713_);
lean_closure_set(v___f_722_, 3, v___y_714_);
lean_closure_set(v___f_722_, 4, v___y_715_);
lean_closure_set(v___f_722_, 5, v___y_716_);
v___x_723_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_710_, v___f_722_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_723_) == 0)
{
return v___x_723_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___boxed(lean_object* v_mvarId_732_, lean_object* v_x_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_732_, v_x_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(lean_object* v_00_u03b1_745_, lean_object* v_mvarId_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_746_, v_x_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed(lean_object* v_00_u03b1_759_, lean_object* v_mvarId_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(v_00_u03b1_759_, v_mvarId_760_, v_x_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(lean_object* v_mvarId_773_, lean_object* v_fst_774_, lean_object* v_snd_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_MVarId_getType(v_mvarId_773_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_789_, 0, v_a_788_);
v___x_790_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_789_, v_fst_774_, v_snd_775_, v___y_776_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_790_;
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___y_776_);
lean_dec(v_snd_775_);
lean_dec_ref(v_fst_774_);
v_a_791_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_787_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_787_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed(lean_object* v_mvarId_799_, lean_object* v_fst_800_, lean_object* v_snd_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(v_mvarId_799_, v_fst_800_, v_snd_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_ks_818_; lean_object* v_vs_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_843_; 
v_ks_818_ = lean_ctor_get(v_x_814_, 0);
v_vs_819_ = lean_ctor_get(v_x_814_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_814_);
if (v_isSharedCheck_843_ == 0)
{
v___x_821_ = v_x_814_;
v_isShared_822_ = v_isSharedCheck_843_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_vs_819_);
lean_inc(v_ks_818_);
lean_dec(v_x_814_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_843_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = lean_array_get_size(v_ks_818_);
v___x_824_ = lean_nat_dec_lt(v_x_815_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_x_815_);
v___x_825_ = lean_array_push(v_ks_818_, v_x_816_);
v___x_826_ = lean_array_push(v_vs_819_, v_x_817_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_826_);
lean_ctor_set(v___x_821_, 0, v___x_825_);
v___x_828_ = v___x_821_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v_k_x27_830_; uint8_t v___x_831_; 
v_k_x27_830_ = lean_array_fget_borrowed(v_ks_818_, v_x_815_);
v___x_831_ = l_Lean_instBEqMVarId_beq(v_x_816_, v_k_x27_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_833_; 
if (v_isShared_822_ == 0)
{
v___x_833_ = v___x_821_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_ks_818_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_vs_819_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(1u);
v___x_835_ = lean_nat_add(v_x_815_, v___x_834_);
lean_dec(v_x_815_);
v_x_814_ = v___x_833_;
v_x_815_ = v___x_835_;
goto _start;
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = lean_array_fset(v_ks_818_, v_x_815_, v_x_816_);
v___x_839_ = lean_array_fset(v_vs_819_, v_x_815_, v_x_817_);
lean_dec(v_x_815_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_839_);
lean_ctor_set(v___x_821_, 0, v___x_838_);
v___x_841_ = v___x_821_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(lean_object* v_n_844_, lean_object* v_k_845_, lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_n_844_, v___x_847_, v_k_845_, v_v_846_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(lean_object* v_x_850_, size_t v_x_851_, size_t v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v_es_855_; size_t v___x_856_; size_t v___x_857_; lean_object* v_j_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_es_855_ = lean_ctor_get(v_x_850_, 0);
v___x_856_ = ((size_t)31ULL);
v___x_857_ = lean_usize_land(v_x_851_, v___x_856_);
v_j_858_ = lean_usize_to_nat(v___x_857_);
v___x_859_ = lean_array_get_size(v_es_855_);
v___x_860_ = lean_nat_dec_lt(v_j_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec(v_j_858_);
lean_dec(v_x_854_);
lean_dec(v_x_853_);
return v_x_850_;
}
else
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_899_; 
lean_inc_ref(v_es_855_);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_x_850_, 0);
lean_dec(v_unused_900_);
v___x_862_ = v_x_850_;
v_isShared_863_ = v_isSharedCheck_899_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_x_850_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_899_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_v_864_; lean_object* v___x_865_; lean_object* v_xs_x27_866_; lean_object* v___y_868_; 
v_v_864_ = lean_array_fget(v_es_855_, v_j_858_);
v___x_865_ = lean_box(0);
v_xs_x27_866_ = lean_array_fset(v_es_855_, v_j_858_, v___x_865_);
switch(lean_obj_tag(v_v_864_))
{
case 0:
{
lean_object* v_key_873_; lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_884_; 
v_key_873_ = lean_ctor_get(v_v_864_, 0);
v_val_874_ = lean_ctor_get(v_v_864_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_v_864_);
if (v_isSharedCheck_884_ == 0)
{
v___x_876_ = v_v_864_;
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_inc(v_key_873_);
lean_dec(v_v_864_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_884_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_instBEqMVarId_beq(v_x_853_, v_key_873_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_del_object(v___x_876_);
v___x_879_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_873_, v_val_874_, v_x_853_, v_x_854_);
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
v___y_868_ = v___x_880_;
goto v___jp_867_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_val_874_);
lean_dec(v_key_873_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_x_854_);
lean_ctor_set(v___x_876_, 0, v_x_853_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_x_853_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_x_854_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
v___y_868_ = v___x_882_;
goto v___jp_867_;
}
}
}
}
case 1:
{
lean_object* v_node_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v_node_885_ = lean_ctor_get(v_v_864_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_v_864_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v_v_864_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_node_885_);
lean_dec(v_v_864_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_889_ = ((size_t)5ULL);
v___x_890_ = lean_usize_shift_right(v_x_851_, v___x_889_);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_x_852_, v___x_891_);
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_node_885_, v___x_890_, v___x_892_, v_x_853_, v_x_854_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_893_);
v___x_895_ = v___x_887_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
v___y_868_ = v___x_895_;
goto v___jp_867_;
}
}
}
default: 
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_x_853_);
lean_ctor_set(v___x_898_, 1, v_x_854_);
v___y_868_ = v___x_898_;
goto v___jp_867_;
}
}
v___jp_867_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_array_fset(v_xs_x27_866_, v_j_858_, v___y_868_);
lean_dec(v_j_858_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_869_);
v___x_871_ = v___x_862_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
else
{
lean_object* v_ks_901_; lean_object* v_vs_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_922_; 
v_ks_901_ = lean_ctor_get(v_x_850_, 0);
v_vs_902_ = lean_ctor_get(v_x_850_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_922_ == 0)
{
v___x_904_ = v_x_850_;
v_isShared_905_ = v_isSharedCheck_922_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_vs_902_);
lean_inc(v_ks_901_);
lean_dec(v_x_850_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_922_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_ks_901_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_vs_902_);
v___x_907_ = v_reuseFailAlloc_921_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v_newNode_908_; uint8_t v___y_910_; size_t v___x_916_; uint8_t v___x_917_; 
v_newNode_908_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v___x_907_, v_x_853_, v_x_854_);
v___x_916_ = ((size_t)7ULL);
v___x_917_ = lean_usize_dec_le(v___x_916_, v_x_852_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_908_);
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
lean_dec(v___x_918_);
v___y_910_ = v___x_920_;
goto v___jp_909_;
}
else
{
v___y_910_ = v___x_917_;
goto v___jp_909_;
}
v___jp_909_:
{
if (v___y_910_ == 0)
{
lean_object* v_ks_911_; lean_object* v_vs_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_ks_911_ = lean_ctor_get(v_newNode_908_, 0);
lean_inc_ref(v_ks_911_);
v_vs_912_ = lean_ctor_get(v_newNode_908_, 1);
lean_inc_ref(v_vs_912_);
lean_dec_ref(v_newNode_908_);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0);
v___x_915_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_x_852_, v_ks_911_, v_vs_912_, v___x_913_, v___x_914_);
lean_dec_ref(v_vs_912_);
lean_dec_ref(v_ks_911_);
return v___x_915_;
}
else
{
return v_newNode_908_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(size_t v_depth_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_i_926_, lean_object* v_entries_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_get_size(v_keys_924_);
v___x_929_ = lean_nat_dec_lt(v_i_926_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec(v_i_926_);
return v_entries_927_;
}
else
{
lean_object* v_k_930_; lean_object* v_v_931_; uint64_t v___x_932_; size_t v_h_933_; size_t v___x_934_; lean_object* v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v_h_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_k_930_ = lean_array_fget_borrowed(v_keys_924_, v_i_926_);
v_v_931_ = lean_array_fget_borrowed(v_vals_925_, v_i_926_);
v___x_932_ = l_Lean_instHashableMVarId_hash(v_k_930_);
v_h_933_ = lean_uint64_to_usize(v___x_932_);
v___x_934_ = ((size_t)5ULL);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_sub(v_depth_923_, v___x_936_);
v___x_938_ = lean_usize_mul(v___x_934_, v___x_937_);
v_h_939_ = lean_usize_shift_right(v_h_933_, v___x_938_);
v___x_940_ = lean_nat_add(v_i_926_, v___x_935_);
lean_dec(v_i_926_);
lean_inc(v_v_931_);
lean_inc(v_k_930_);
v___x_941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_entries_927_, v_h_939_, v_depth_923_, v_k_930_, v_v_931_);
v_i_926_ = v___x_940_;
v_entries_927_ = v___x_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_943_, lean_object* v_keys_944_, lean_object* v_vals_945_, lean_object* v_i_946_, lean_object* v_entries_947_){
_start:
{
size_t v_depth_boxed_948_; lean_object* v_res_949_; 
v_depth_boxed_948_ = lean_unbox_usize(v_depth_943_);
lean_dec(v_depth_943_);
v_res_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_boxed_948_, v_keys_944_, v_vals_945_, v_i_946_, v_entries_947_);
lean_dec_ref(v_vals_945_);
lean_dec_ref(v_keys_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
size_t v_x_11104__boxed_955_; size_t v_x_11105__boxed_956_; lean_object* v_res_957_; 
v_x_11104__boxed_955_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_x_11105__boxed_956_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_950_, v_x_11104__boxed_955_, v_x_11105__boxed_956_, v_x_953_, v_x_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
uint64_t v___x_961_; size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_961_ = l_Lean_instHashableMVarId_hash(v_x_959_);
v___x_962_ = lean_uint64_to_usize(v___x_961_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_958_, v___x_962_, v___x_963_, v_x_959_, v_x_960_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object* v_mvarId_965_, lean_object* v_val_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_mctx_970_; lean_object* v_cache_971_; lean_object* v_zetaDeltaFVarIds_972_; lean_object* v_postponed_973_; lean_object* v_diag_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1002_; 
v___x_969_ = lean_st_ref_take(v___y_967_);
v_mctx_970_ = lean_ctor_get(v___x_969_, 0);
v_cache_971_ = lean_ctor_get(v___x_969_, 1);
v_zetaDeltaFVarIds_972_ = lean_ctor_get(v___x_969_, 2);
v_postponed_973_ = lean_ctor_get(v___x_969_, 3);
v_diag_974_ = lean_ctor_get(v___x_969_, 4);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_976_ = v___x_969_;
v_isShared_977_ = v_isSharedCheck_1002_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_diag_974_);
lean_inc(v_postponed_973_);
lean_inc(v_zetaDeltaFVarIds_972_);
lean_inc(v_cache_971_);
lean_inc(v_mctx_970_);
lean_dec(v___x_969_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1002_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_depth_978_; lean_object* v_levelAssignDepth_979_; lean_object* v_lmvarCounter_980_; lean_object* v_mvarCounter_981_; lean_object* v_lDecls_982_; lean_object* v_decls_983_; lean_object* v_userNames_984_; lean_object* v_lAssignment_985_; lean_object* v_eAssignment_986_; lean_object* v_dAssignment_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1001_; 
v_depth_978_ = lean_ctor_get(v_mctx_970_, 0);
v_levelAssignDepth_979_ = lean_ctor_get(v_mctx_970_, 1);
v_lmvarCounter_980_ = lean_ctor_get(v_mctx_970_, 2);
v_mvarCounter_981_ = lean_ctor_get(v_mctx_970_, 3);
v_lDecls_982_ = lean_ctor_get(v_mctx_970_, 4);
v_decls_983_ = lean_ctor_get(v_mctx_970_, 5);
v_userNames_984_ = lean_ctor_get(v_mctx_970_, 6);
v_lAssignment_985_ = lean_ctor_get(v_mctx_970_, 7);
v_eAssignment_986_ = lean_ctor_get(v_mctx_970_, 8);
v_dAssignment_987_ = lean_ctor_get(v_mctx_970_, 9);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_mctx_970_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_989_ = v_mctx_970_;
v_isShared_990_ = v_isSharedCheck_1001_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_dAssignment_987_);
lean_inc(v_eAssignment_986_);
lean_inc(v_lAssignment_985_);
lean_inc(v_userNames_984_);
lean_inc(v_decls_983_);
lean_inc(v_lDecls_982_);
lean_inc(v_mvarCounter_981_);
lean_inc(v_lmvarCounter_980_);
lean_inc(v_levelAssignDepth_979_);
lean_inc(v_depth_978_);
lean_dec(v_mctx_970_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1001_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_eAssignment_986_, v_mvarId_965_, v_val_966_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 8, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_depth_978_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_levelAssignDepth_979_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_lmvarCounter_980_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_mvarCounter_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_lDecls_982_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v_decls_983_);
lean_ctor_set(v_reuseFailAlloc_1000_, 6, v_userNames_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 7, v_lAssignment_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 8, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1000_, 9, v_dAssignment_987_);
v___x_993_ = v_reuseFailAlloc_1000_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_993_);
v___x_995_ = v___x_976_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_cache_971_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_zetaDeltaFVarIds_972_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_postponed_973_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_diag_974_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_st_ref_set(v___y_967_, v___x_995_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object* v_mvarId_1003_, lean_object* v_val_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1003_, v_val_1004_, v___y_1005_);
lean_dec(v___y_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object* v_a_1008_, lean_object* v_x_1009_){
_start:
{
if (lean_obj_tag(v_x_1009_) == 0)
{
uint8_t v___x_1010_; 
v___x_1010_ = 0;
return v___x_1010_;
}
else
{
lean_object* v_key_1011_; lean_object* v_tail_1012_; uint8_t v___x_1013_; 
v_key_1011_ = lean_ctor_get(v_x_1009_, 0);
v_tail_1012_ = lean_ctor_get(v_x_1009_, 2);
v___x_1013_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1011_, v_a_1008_);
if (v___x_1013_ == 0)
{
v_x_1009_ = v_tail_1012_;
goto _start;
}
else
{
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg___boxed(lean_object* v_a_1015_, lean_object* v_x_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec_ref(v_a_1015_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(lean_object* v_a_1019_, lean_object* v_b_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_dec(v_b_1020_);
lean_dec_ref(v_a_1019_);
return v_x_1021_;
}
else
{
lean_object* v_key_1022_; lean_object* v_value_1023_; lean_object* v_tail_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1036_; 
v_key_1022_ = lean_ctor_get(v_x_1021_, 0);
v_value_1023_ = lean_ctor_get(v_x_1021_, 1);
v_tail_1024_ = lean_ctor_get(v_x_1021_, 2);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1026_ = v_x_1021_;
v_isShared_1027_ = v_isSharedCheck_1036_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_tail_1024_);
lean_inc(v_value_1023_);
lean_inc(v_key_1022_);
lean_dec(v_x_1021_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1036_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint8_t v___x_1028_; 
v___x_1028_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1022_, v_a_1019_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1019_, v_b_1020_, v_tail_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 2, v___x_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_key_1022_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_value_1023_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_value_1023_);
lean_dec(v_key_1022_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_b_1020_);
lean_ctor_set(v___x_1026_, 0, v_a_1019_);
v___x_1034_ = v___x_1026_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1019_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_b_1020_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_tail_1024_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
return v_x_1037_;
}
else
{
lean_object* v_key_1039_; lean_object* v_value_1040_; lean_object* v_tail_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1064_; 
v_key_1039_ = lean_ctor_get(v_x_1038_, 0);
v_value_1040_ = lean_ctor_get(v_x_1038_, 1);
v_tail_1041_ = lean_ctor_get(v_x_1038_, 2);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1038_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1043_ = v_x_1038_;
v_isShared_1044_ = v_isSharedCheck_1064_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_tail_1041_);
lean_inc(v_value_1040_);
lean_inc(v_key_1039_);
lean_dec(v_x_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1064_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v___x_1048_; uint64_t v_fold_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1045_ = lean_array_get_size(v_x_1037_);
v___x_1046_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_key_1039_);
v___x_1047_ = 32ULL;
v___x_1048_ = lean_uint64_shift_right(v___x_1046_, v___x_1047_);
v_fold_1049_ = lean_uint64_xor(v___x_1046_, v___x_1048_);
v___x_1050_ = 16ULL;
v___x_1051_ = lean_uint64_shift_right(v_fold_1049_, v___x_1050_);
v___x_1052_ = lean_uint64_xor(v_fold_1049_, v___x_1051_);
v___x_1053_ = lean_uint64_to_usize(v___x_1052_);
v___x_1054_ = lean_usize_of_nat(v___x_1045_);
v___x_1055_ = ((size_t)1ULL);
v___x_1056_ = lean_usize_sub(v___x_1054_, v___x_1055_);
v___x_1057_ = lean_usize_land(v___x_1053_, v___x_1056_);
v___x_1058_ = lean_array_uget_borrowed(v_x_1037_, v___x_1057_);
lean_inc(v___x_1058_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 2, v___x_1058_);
v___x_1060_ = v___x_1043_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_key_1039_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_value_1040_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_array_uset(v_x_1037_, v___x_1057_, v___x_1060_);
v_x_1037_ = v___x_1061_;
v_x_1038_ = v_tail_1041_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1065_, lean_object* v_source_1066_, lean_object* v_target_1067_){
_start:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_array_get_size(v_source_1066_);
v___x_1069_ = lean_nat_dec_lt(v_i_1065_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec_ref(v_source_1066_);
lean_dec(v_i_1065_);
return v_target_1067_;
}
else
{
lean_object* v_es_1070_; lean_object* v___x_1071_; lean_object* v_source_1072_; lean_object* v_target_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_es_1070_ = lean_array_fget(v_source_1066_, v_i_1065_);
v___x_1071_ = lean_box(0);
v_source_1072_ = lean_array_fset(v_source_1066_, v_i_1065_, v___x_1071_);
v_target_1073_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1067_, v_es_1070_);
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_nat_add(v_i_1065_, v___x_1074_);
lean_dec(v_i_1065_);
v_i_1065_ = v___x_1075_;
v_source_1066_ = v_source_1072_;
v_target_1067_ = v_target_1073_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(lean_object* v_data_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_nbuckets_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1078_ = lean_array_get_size(v_data_1077_);
v___x_1079_ = lean_unsigned_to_nat(2u);
v_nbuckets_1080_ = lean_nat_mul(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_mk_array(v_nbuckets_1080_, v___x_1082_);
v___x_1084_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v___x_1081_, v_data_1077_, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object* v_m_1085_, lean_object* v_a_1086_, lean_object* v_b_1087_){
_start:
{
lean_object* v_size_1088_; lean_object* v_buckets_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1132_; 
v_size_1088_ = lean_ctor_get(v_m_1085_, 0);
v_buckets_1089_ = lean_ctor_get(v_m_1085_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_m_1085_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1091_ = v_m_1085_;
v_isShared_1092_ = v_isSharedCheck_1132_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_buckets_1089_);
lean_inc(v_size_1088_);
lean_dec(v_m_1085_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1132_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v_fold_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v_bkt_1106_; uint8_t v___x_1107_; 
v___x_1093_ = lean_array_get_size(v_buckets_1089_);
v___x_1094_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1086_);
v___x_1095_ = 32ULL;
v___x_1096_ = lean_uint64_shift_right(v___x_1094_, v___x_1095_);
v_fold_1097_ = lean_uint64_xor(v___x_1094_, v___x_1096_);
v___x_1098_ = 16ULL;
v___x_1099_ = lean_uint64_shift_right(v_fold_1097_, v___x_1098_);
v___x_1100_ = lean_uint64_xor(v_fold_1097_, v___x_1099_);
v___x_1101_ = lean_uint64_to_usize(v___x_1100_);
v___x_1102_ = lean_usize_of_nat(v___x_1093_);
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_sub(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_usize_land(v___x_1101_, v___x_1104_);
v_bkt_1106_ = lean_array_uget_borrowed(v_buckets_1089_, v___x_1105_);
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1086_, v_bkt_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v_size_x27_1109_; lean_object* v___x_1110_; lean_object* v_buckets_x27_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1108_ = lean_unsigned_to_nat(1u);
v_size_x27_1109_ = lean_nat_add(v_size_1088_, v___x_1108_);
lean_dec(v_size_1088_);
lean_inc(v_bkt_1106_);
v___x_1110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1110_, 0, v_a_1086_);
lean_ctor_set(v___x_1110_, 1, v_b_1087_);
lean_ctor_set(v___x_1110_, 2, v_bkt_1106_);
v_buckets_x27_1111_ = lean_array_uset(v_buckets_1089_, v___x_1105_, v___x_1110_);
v___x_1112_ = lean_unsigned_to_nat(4u);
v___x_1113_ = lean_nat_mul(v_size_x27_1109_, v___x_1112_);
v___x_1114_ = lean_unsigned_to_nat(3u);
v___x_1115_ = lean_nat_div(v___x_1113_, v___x_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_array_get_size(v_buckets_x27_1111_);
v___x_1117_ = lean_nat_dec_le(v___x_1115_, v___x_1116_);
lean_dec(v___x_1115_);
if (v___x_1117_ == 0)
{
lean_object* v_val_1118_; lean_object* v___x_1120_; 
v_val_1118_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_buckets_x27_1111_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_val_1118_);
lean_ctor_set(v___x_1091_, 0, v_size_x27_1109_);
v___x_1120_ = v___x_1091_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_size_x27_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_val_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1123_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_buckets_x27_1111_);
lean_ctor_set(v___x_1091_, 0, v_size_x27_1109_);
v___x_1123_ = v___x_1091_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_size_x27_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_buckets_x27_1111_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v___x_1125_; lean_object* v_buckets_x27_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_inc(v_bkt_1106_);
v___x_1125_ = lean_box(0);
v_buckets_x27_1126_ = lean_array_uset(v_buckets_1089_, v___x_1105_, v___x_1125_);
v___x_1127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1086_, v_b_1087_, v_bkt_1106_);
v___x_1128_ = lean_array_uset(v_buckets_x27_1126_, v___x_1105_, v___x_1127_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1128_);
v___x_1130_ = v___x_1091_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_size_1088_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(lean_object* v_a_1133_, lean_object* v_x_1134_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
lean_object* v_key_1136_; lean_object* v_value_1137_; lean_object* v_tail_1138_; uint8_t v___x_1139_; 
v_key_1136_ = lean_ctor_get(v_x_1134_, 0);
v_value_1137_ = lean_ctor_get(v_x_1134_, 1);
v_tail_1138_ = lean_ctor_get(v_x_1134_, 2);
v___x_1139_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1136_, v_a_1133_);
if (v___x_1139_ == 0)
{
v_x_1134_ = v_tail_1138_;
goto _start;
}
else
{
lean_object* v___x_1141_; 
lean_inc(v_value_1137_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_value_1137_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg___boxed(lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1142_, v_x_1143_);
lean_dec(v_x_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object* v_m_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_buckets_1147_; lean_object* v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; uint64_t v_fold_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_buckets_1147_ = lean_ctor_get(v_m_1145_, 1);
v___x_1148_ = lean_array_get_size(v_buckets_1147_);
v___x_1149_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1146_);
v___x_1150_ = 32ULL;
v___x_1151_ = lean_uint64_shift_right(v___x_1149_, v___x_1150_);
v_fold_1152_ = lean_uint64_xor(v___x_1149_, v___x_1151_);
v___x_1153_ = 16ULL;
v___x_1154_ = lean_uint64_shift_right(v_fold_1152_, v___x_1153_);
v___x_1155_ = lean_uint64_xor(v_fold_1152_, v___x_1154_);
v___x_1156_ = lean_uint64_to_usize(v___x_1155_);
v___x_1157_ = lean_usize_of_nat(v___x_1148_);
v___x_1158_ = ((size_t)1ULL);
v___x_1159_ = lean_usize_sub(v___x_1157_, v___x_1158_);
v___x_1160_ = lean_usize_land(v___x_1156_, v___x_1159_);
v___x_1161_ = lean_array_uget_borrowed(v_buckets_1147_, v___x_1160_);
v___x_1162_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1146_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object* v_m_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1163_, v_a_1164_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_m_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(uint8_t v___x_1166_, uint8_t v___x_1167_, lean_object* v_as_1168_, size_t v_i_1169_, size_t v_stop_1170_, lean_object* v_b_1171_){
_start:
{
lean_object* v___y_1173_; uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_eq(v_i_1169_, v_stop_1170_);
if (v___x_1177_ == 0)
{
lean_object* v_fst_1178_; uint8_t v___x_1179_; 
v_fst_1178_ = lean_ctor_get(v_b_1171_, 0);
v___x_1179_ = lean_unbox(v_fst_1178_);
if (v___x_1179_ == 0)
{
lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
v_snd_1180_ = lean_ctor_get(v_b_1171_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_b_1171_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_b_1171_, 0);
lean_dec(v_unused_1189_);
v___x_1182_ = v_b_1171_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_dec(v_b_1171_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_box(v___x_1166_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_snd_1180_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
v___y_1173_ = v___x_1186_;
goto v___jp_1172_;
}
}
}
else
{
lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1200_; 
v_snd_1190_ = lean_ctor_get(v_b_1171_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_b_1171_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_b_1171_, 0);
lean_dec(v_unused_1201_);
v___x_1192_ = v_b_1171_;
v_isShared_1193_ = v_isSharedCheck_1200_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_dec(v_b_1171_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1200_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1194_ = lean_array_uget_borrowed(v_as_1168_, v_i_1169_);
lean_inc(v___x_1194_);
v___x_1195_ = lean_array_push(v_snd_1190_, v___x_1194_);
v___x_1196_ = lean_box(v___x_1167_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1195_);
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1198_ = v___x_1192_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1195_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
v___y_1173_ = v___x_1198_;
goto v___jp_1172_;
}
}
}
}
else
{
return v_b_1171_;
}
v___jp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1169_, v___x_1174_);
v_i_1169_ = v___x_1175_;
v_b_1171_ = v___y_1173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_as_1204_, lean_object* v_i_1205_, lean_object* v_stop_1206_, lean_object* v_b_1207_){
_start:
{
uint8_t v___x_11569__boxed_1208_; uint8_t v___x_11570__boxed_1209_; size_t v_i_boxed_1210_; size_t v_stop_boxed_1211_; lean_object* v_res_1212_; 
v___x_11569__boxed_1208_ = lean_unbox(v___x_1202_);
v___x_11570__boxed_1209_ = lean_unbox(v___x_1203_);
v_i_boxed_1210_ = lean_unbox_usize(v_i_1205_);
lean_dec(v_i_1205_);
v_stop_boxed_1211_ = lean_unbox_usize(v_stop_1206_);
lean_dec(v_stop_1206_);
v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_11569__boxed_1208_, v___x_11570__boxed_1209_, v_as_1204_, v_i_boxed_1210_, v_stop_boxed_1211_, v_b_1207_);
lean_dec_ref(v_as_1204_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(size_t v_sz_1213_, size_t v_i_1214_, lean_object* v_bs_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_lt(v_i_1214_, v_sz_1213_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_bs_1215_);
return v___x_1217_;
}
else
{
lean_object* v_v_1218_; lean_object* v___x_1219_; lean_object* v_bs_x27_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; 
v_v_1218_ = lean_array_uget(v_bs_1215_, v_i_1214_);
v___x_1219_ = lean_unsigned_to_nat(0u);
v_bs_x27_1220_ = lean_array_uset(v_bs_1215_, v_i_1214_, v___x_1219_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1214_, v___x_1221_);
v___x_1223_ = lean_array_uset(v_bs_x27_1220_, v_i_1214_, v_v_1218_);
v_i_1214_ = v___x_1222_;
v_bs_1215_ = v___x_1223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object* v_sz_1225_, lean_object* v_i_1226_, lean_object* v_bs_1227_){
_start:
{
size_t v_sz_boxed_1228_; size_t v_i_boxed_1229_; lean_object* v_res_1230_; 
v_sz_boxed_1228_ = lean_unbox_usize(v_sz_1225_);
lean_dec(v_sz_1225_);
v_i_boxed_1229_ = lean_unbox_usize(v_i_1226_);
lean_dec(v_i_1226_);
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_boxed_1228_, v_i_boxed_1229_, v_bs_1227_);
return v_res_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4));
v___x_1241_ = l_Lean_mkConst(v___x_1240_, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(lean_object* v_stx_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_1262_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1394_, 0);
lean_dec(v_unused_1503_);
v___x_1396_ = v___x_1394_;
v_isShared_1397_ = v_isSharedCheck_1502_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v___x_1394_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1502_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
lean_inc(v_stx_1261_);
v___x_1399_ = l_Lean_Syntax_isOfKind(v_stx_1261_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_del_object(v___x_1396_);
lean_dec(v_stx_1261_);
v___x_1400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1431_; lean_object* v_args_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___x_1459_; lean_object* v_variantId_x3f_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1493_ = l_Lean_Syntax_getArg(v_stx_1261_, v___x_1459_);
v___x_1494_ = l_Lean_Syntax_isNone(v___x_1493_);
if (v___x_1494_ == 0)
{
uint8_t v___x_1495_; 
lean_inc(v___x_1493_);
v___x_1495_ = l_Lean_Syntax_matchesNull(v___x_1493_, v___x_1459_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
lean_dec(v___x_1493_);
lean_del_object(v___x_1396_);
lean_dec(v_stx_1261_);
v___x_1496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = l_Lean_Syntax_getArg(v___x_1493_, v___x_1401_);
lean_dec(v___x_1493_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 1);
lean_ctor_set(v___x_1396_, 0, v___x_1497_);
v___x_1499_ = v___x_1396_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
v_variantId_x3f_1461_ = v___x_1499_;
v___y_1462_ = v___y_1262_;
v___y_1463_ = v___y_1263_;
v___y_1464_ = v___y_1264_;
v___y_1465_ = v___y_1265_;
v___y_1466_ = v___y_1266_;
v___y_1467_ = v___y_1267_;
v___y_1468_ = v___y_1268_;
v___y_1469_ = v___y_1269_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v___x_1501_; 
lean_dec(v___x_1493_);
lean_del_object(v___x_1396_);
v___x_1501_ = lean_box(0);
v_variantId_x3f_1461_ = v___x_1501_;
v___y_1462_ = v___y_1262_;
v___y_1463_ = v___y_1263_;
v___y_1464_ = v___y_1264_;
v___y_1465_ = v___y_1265_;
v___y_1466_ = v___y_1266_;
v___y_1467_ = v___y_1267_;
v___y_1468_ = v___y_1268_;
v___y_1469_ = v___y_1269_;
goto v___jp_1460_;
}
v___jp_1402_:
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v___y_1407_, v___y_1403_, v___y_1411_, v___y_1405_, v___y_1406_, v___y_1408_, v___y_1410_, v___y_1409_, v___y_1404_);
lean_dec(v___y_1407_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; lean_object* v_cache_1416_; lean_object* v_dsimpState_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc_n(v_a_1414_, 2);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = lean_st_ref_get(v___y_1411_);
v_cache_1416_ = lean_ctor_get(v___x_1415_, 3);
lean_inc_ref(v_cache_1416_);
lean_dec(v___x_1415_);
v_dsimpState_1417_ = lean_ctor_get(v_cache_1416_, 3);
lean_inc_ref(v_dsimpState_1417_);
lean_dec_ref(v_cache_1416_);
lean_inc(v___y_1412_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___y_1412_);
lean_ctor_set(v___x_1418_, 1, v_a_1414_);
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_dsimpState_1417_, v___x_1418_);
lean_dec_ref(v_dsimpState_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14);
v___y_1272_ = v___y_1403_;
v___y_1273_ = v___y_1404_;
v___y_1274_ = v___y_1405_;
v___y_1275_ = v___y_1406_;
v___y_1276_ = v_a_1414_;
v___y_1277_ = v___x_1418_;
v___y_1278_ = v___y_1412_;
v___y_1279_ = v___y_1408_;
v___y_1280_ = v___y_1409_;
v___y_1281_ = v___y_1410_;
v___y_1282_ = v___y_1411_;
v___y_1283_ = v___x_1420_;
goto v___jp_1271_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1421_);
lean_dec_ref_known(v___x_1419_, 1);
v___y_1272_ = v___y_1403_;
v___y_1273_ = v___y_1404_;
v___y_1274_ = v___y_1405_;
v___y_1275_ = v___y_1406_;
v___y_1276_ = v_a_1414_;
v___y_1277_ = v___x_1418_;
v___y_1278_ = v___y_1412_;
v___y_1279_ = v___y_1408_;
v___y_1280_ = v___y_1409_;
v___y_1281_ = v___y_1410_;
v___y_1282_ = v___y_1411_;
v___y_1283_ = v_val_1421_;
goto v___jp_1271_;
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v___y_1412_);
v_a_1422_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1413_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1413_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
v___jp_1430_:
{
if (lean_obj_tag(v___y_1431_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_box(0);
v___y_1403_ = v___y_1433_;
v___y_1404_ = v___y_1440_;
v___y_1405_ = v___y_1435_;
v___y_1406_ = v___y_1436_;
v___y_1407_ = v_args_1432_;
v___y_1408_ = v___y_1437_;
v___y_1409_ = v___y_1439_;
v___y_1410_ = v___y_1438_;
v___y_1411_ = v___y_1434_;
v___y_1412_ = v___x_1441_;
goto v___jp_1402_;
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1443_; 
v_val_1442_ = lean_ctor_get(v___y_1431_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___y_1431_, 1);
v___x_1443_ = l_Lean_TSyntax_getId(v_val_1442_);
lean_dec(v_val_1442_);
v___y_1403_ = v___y_1433_;
v___y_1404_ = v___y_1440_;
v___y_1405_ = v___y_1435_;
v___y_1406_ = v___y_1436_;
v___y_1407_ = v_args_1432_;
v___y_1408_ = v___y_1437_;
v___y_1409_ = v___y_1439_;
v___y_1410_ = v___y_1438_;
v___y_1411_ = v___y_1434_;
v___y_1412_ = v___x_1443_;
goto v___jp_1402_;
}
}
v___jp_1444_:
{
size_t v_sz_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v_sz_1455_ = lean_array_size(v___y_1454_);
v___x_1456_ = ((size_t)0ULL);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_1455_, v___x_1456_, v___y_1454_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1458_; 
lean_dec(v___y_1451_);
v___x_1458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1458_;
}
else
{
v___y_1431_ = v___y_1451_;
v_args_1432_ = v___x_1457_;
v___y_1433_ = v___y_1447_;
v___y_1434_ = v___y_1445_;
v___y_1435_ = v___y_1446_;
v___y_1436_ = v___y_1453_;
v___y_1437_ = v___y_1448_;
v___y_1438_ = v___y_1452_;
v___y_1439_ = v___y_1449_;
v___y_1440_ = v___y_1450_;
goto v___jp_1430_;
}
}
v___jp_1460_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_unsigned_to_nat(2u);
v___x_1471_ = l_Lean_Syntax_getArg(v_stx_1261_, v___x_1470_);
lean_dec(v_stx_1261_);
v___x_1472_ = l_Lean_Syntax_isNone(v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1471_);
v___x_1474_ = l_Lean_Syntax_matchesNull(v___x_1471_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec(v___x_1471_);
lean_dec(v_variantId_x3f_1461_);
v___x_1475_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1476_ = l_Lean_Syntax_getArg(v___x_1471_, v___x_1459_);
lean_dec(v___x_1471_);
v___x_1477_ = l_Lean_Syntax_getArgs(v___x_1476_);
lean_dec(v___x_1476_);
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15));
v___x_1479_ = lean_array_get_size(v___x_1477_);
v___x_1480_ = lean_nat_dec_lt(v___x_1401_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_dec_ref(v___x_1477_);
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1464_;
v___y_1447_ = v___y_1462_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v_variantId_x3f_1461_;
v___y_1452_ = v___y_1467_;
v___y_1453_ = v___y_1465_;
v___y_1454_ = v___x_1478_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = lean_box(v___x_1474_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1478_);
v___x_1483_ = lean_nat_dec_le(v___x_1479_, v___x_1479_);
if (v___x_1483_ == 0)
{
if (v___x_1480_ == 0)
{
lean_dec_ref_known(v___x_1482_, 2);
lean_dec_ref(v___x_1477_);
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1464_;
v___y_1447_ = v___y_1462_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v_variantId_x3f_1461_;
v___y_1452_ = v___y_1467_;
v___y_1453_ = v___y_1465_;
v___y_1454_ = v___x_1478_;
goto v___jp_1444_;
}
else
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; lean_object* v_snd_1487_; 
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = lean_usize_of_nat(v___x_1479_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_1474_, v___x_1472_, v___x_1477_, v___x_1484_, v___x_1485_, v___x_1482_);
lean_dec_ref(v___x_1477_);
v_snd_1487_ = lean_ctor_get(v___x_1486_, 1);
lean_inc(v_snd_1487_);
lean_dec_ref(v___x_1486_);
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1464_;
v___y_1447_ = v___y_1462_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v_variantId_x3f_1461_;
v___y_1452_ = v___y_1467_;
v___y_1453_ = v___y_1465_;
v___y_1454_ = v_snd_1487_;
goto v___jp_1444_;
}
}
else
{
size_t v___x_1488_; size_t v___x_1489_; lean_object* v___x_1490_; lean_object* v_snd_1491_; 
v___x_1488_ = ((size_t)0ULL);
v___x_1489_ = lean_usize_of_nat(v___x_1479_);
v___x_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_1474_, v___x_1472_, v___x_1477_, v___x_1488_, v___x_1489_, v___x_1482_);
lean_dec_ref(v___x_1477_);
v_snd_1491_ = lean_ctor_get(v___x_1490_, 1);
lean_inc(v_snd_1491_);
lean_dec_ref(v___x_1490_);
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1464_;
v___y_1447_ = v___y_1462_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v_variantId_x3f_1461_;
v___y_1452_ = v___y_1467_;
v___y_1453_ = v___y_1465_;
v___y_1454_ = v_snd_1491_;
goto v___jp_1444_;
}
}
}
}
else
{
lean_object* v___x_1492_; 
lean_dec(v___x_1471_);
v___x_1492_ = lean_box(0);
v___y_1431_ = v_variantId_x3f_1461_;
v_args_1432_ = v___x_1492_;
v___y_1433_ = v___y_1462_;
v___y_1434_ = v___y_1463_;
v___y_1435_ = v___y_1464_;
v___y_1436_ = v___y_1465_;
v___y_1437_ = v___y_1466_;
v___y_1438_ = v___y_1467_;
v___y_1439_ = v___y_1468_;
v___y_1440_ = v___y_1469_;
goto v___jp_1430_;
}
}
}
}
}
else
{
lean_dec(v_stx_1261_);
return v___x_1394_;
}
v___jp_1271_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v___y_1278_, v___y_1276_, v___y_1272_, v___y_1282_, v___y_1274_, v___y_1275_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_fst_1286_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_fst_1286_);
v_snd_1287_ = lean_ctor_get(v_a_1285_, 1);
lean_inc(v_snd_1287_);
lean_dec(v_a_1285_);
v___x_1288_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1282_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_toGoalState_1290_; lean_object* v_mvarId_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1377_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_toGoalState_1290_ = lean_ctor_get(v_a_1289_, 0);
v_mvarId_1291_ = lean_ctor_get(v_a_1289_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1293_ = v_a_1289_;
v_isShared_1294_ = v_isSharedCheck_1377_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_mvarId_1291_);
lean_inc(v_toGoalState_1290_);
lean_dec(v_a_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1377_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_inc_n(v_mvarId_1291_, 2);
v___f_1295_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1295_, 0, v_mvarId_1291_);
lean_closure_set(v___f_1295_, 1, v_fst_1286_);
lean_closure_set(v___f_1295_, 2, v_snd_1287_);
lean_closure_set(v___f_1295_, 3, v___y_1283_);
v___x_1296_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed), 13, 3);
lean_closure_set(v___x_1296_, 0, lean_box(0));
lean_closure_set(v___x_1296_, 1, v_mvarId_1291_);
lean_closure_set(v___x_1296_, 2, v___f_1295_);
v___x_1297_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1296_, v___y_1272_, v___y_1282_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1368_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v_fst_1299_ = lean_ctor_get(v_a_1298_, 0);
v_snd_1300_ = lean_ctor_get(v_a_1298_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_a_1298_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1302_ = v_a_1298_;
v_isShared_1303_ = v_isSharedCheck_1368_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_inc(v_fst_1299_);
lean_dec(v_a_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1368_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v_cache_1305_; lean_object* v_symState_1306_; lean_object* v_grindState_1307_; lean_object* v_goals_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1367_; 
v___x_1304_ = lean_st_ref_take(v___y_1282_);
v_cache_1305_ = lean_ctor_get(v___x_1304_, 3);
v_symState_1306_ = lean_ctor_get(v___x_1304_, 0);
v_grindState_1307_ = lean_ctor_get(v___x_1304_, 1);
v_goals_1308_ = lean_ctor_get(v___x_1304_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1310_ = v___x_1304_;
v_isShared_1311_ = v_isSharedCheck_1367_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_cache_1305_);
lean_inc(v_goals_1308_);
lean_inc(v_grindState_1307_);
lean_inc(v_symState_1306_);
lean_dec(v___x_1304_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1367_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_backwardRuleName_1312_; lean_object* v_backwardRuleSyntax_1313_; lean_object* v_simpState_1314_; lean_object* v_dsimpState_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1366_; 
v_backwardRuleName_1312_ = lean_ctor_get(v_cache_1305_, 0);
v_backwardRuleSyntax_1313_ = lean_ctor_get(v_cache_1305_, 1);
v_simpState_1314_ = lean_ctor_get(v_cache_1305_, 2);
v_dsimpState_1315_ = lean_ctor_get(v_cache_1305_, 3);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_cache_1305_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1317_ = v_cache_1305_;
v_isShared_1318_ = v_isSharedCheck_1366_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_dsimpState_1315_);
lean_inc(v_simpState_1314_);
lean_inc(v_backwardRuleSyntax_1313_);
lean_inc(v_backwardRuleName_1312_);
lean_dec(v_cache_1305_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1366_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_dsimpState_1315_, v___y_1277_, v_snd_1300_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 3, v___x_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_backwardRuleName_1312_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_backwardRuleSyntax_1313_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_simpState_1314_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 3, v___x_1321_);
v___x_1323_ = v___x_1310_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_symState_1306_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_grindState_1307_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_goals_1308_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_st_ref_set(v___y_1282_, v___x_1323_);
if (lean_obj_tag(v_fst_1299_) == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref_known(v_fst_1299_, 0);
lean_del_object(v___x_1302_);
lean_del_object(v___x_1293_);
lean_dec(v_mvarId_1291_);
lean_dec_ref(v_toGoalState_1290_);
v___x_1325_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1);
v___x_1326_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_1325_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
return v___x_1326_;
}
else
{
lean_object* v_e_x27_1327_; uint8_t v___x_1328_; 
v_e_x27_1327_ = lean_ctor_get(v_fst_1299_, 0);
lean_inc_ref_n(v_e_x27_1327_, 2);
lean_dec_ref_known(v_fst_1299_, 1);
v___x_1328_ = l_Lean_Expr_isTrue(v_e_x27_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_inc(v_mvarId_1291_);
v___x_1329_ = l_Lean_MVarId_getDecl(v_mvarId_1291_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_userName_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v_userName_1331_ = lean_ctor_get(v_a_1330_, 0);
lean_inc(v_userName_1331_);
lean_dec(v_a_1330_);
v___x_1332_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_1327_, v_userName_1331_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_n(v_a_1333_, 2);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1291_, v_a_1333_, v___y_1281_);
lean_dec_ref(v___x_1334_);
v___x_1335_ = l_Lean_Expr_mvarId_x21(v_a_1333_);
lean_dec(v_a_1333_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___x_1335_);
v___x_1337_ = v___x_1293_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_toGoalState_1290_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_box(0);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 1);
lean_ctor_set(v___x_1302_, 1, v___x_1338_);
lean_ctor_set(v___x_1302_, 0, v___x_1337_);
v___x_1340_ = v___x_1302_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1340_, v___y_1282_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_del_object(v___x_1302_);
lean_del_object(v___x_1293_);
lean_dec(v_mvarId_1291_);
lean_dec_ref(v_toGoalState_1290_);
v_a_1344_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1332_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1332_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_e_x27_1327_);
lean_del_object(v___x_1302_);
lean_del_object(v___x_1293_);
lean_dec(v_mvarId_1291_);
lean_dec_ref(v_toGoalState_1290_);
v_a_1352_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1329_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1329_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v_e_x27_1327_);
lean_del_object(v___x_1302_);
lean_del_object(v___x_1293_);
lean_dec_ref(v_toGoalState_1290_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5);
v___x_1362_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1291_, v___x_1361_, v___y_1281_);
lean_dec_ref(v___x_1362_);
v___x_1363_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1360_, v___y_1282_, v___y_1279_, v___y_1281_, v___y_1280_, v___y_1273_);
return v___x_1363_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_del_object(v___x_1293_);
lean_dec(v_mvarId_1291_);
lean_dec_ref(v_toGoalState_1290_);
lean_dec_ref(v___y_1277_);
v_a_1369_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1297_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1297_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_snd_1287_);
lean_dec(v_fst_1286_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___y_1277_);
v_a_1378_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1288_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1288_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___y_1277_);
v_a_1386_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1284_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1284_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed(lean_object* v_stx_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(v_stx_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(lean_object* v_stx_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___f_1525_; lean_object* v___x_1526_; 
v___f_1525_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1525_, 0, v_stx_1515_);
v___x_1526_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1525_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed(lean_object* v_stx_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(v_stx_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object* v_00_u03b2_1538_, lean_object* v_m_1539_, lean_object* v_a_1540_, lean_object* v_b_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_m_1539_, v_a_1540_, v_b_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object* v_mvarId_1543_, lean_object* v_val_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1543_, v_val_1544_, v___y_1550_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object* v_mvarId_1555_, lean_object* v_val_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(v_mvarId_1555_, v_val_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object* v_00_u03b2_1567_, lean_object* v_m_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1568_, v_a_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object* v_00_u03b2_1571_, lean_object* v_m_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(v_00_u03b2_1571_, v_m_1572_, v_a_1573_);
lean_dec_ref(v_a_1573_);
lean_dec_ref(v_m_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object* v_00_u03b2_1575_, lean_object* v_a_1576_, lean_object* v_x_1577_){
_start:
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1576_, v_x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1579_, lean_object* v_a_1580_, lean_object* v_x_1581_){
_start:
{
uint8_t v_res_1582_; lean_object* v_r_1583_; 
v_res_1582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(v_00_u03b2_1579_, v_a_1580_, v_x_1581_);
lean_dec(v_x_1581_);
lean_dec_ref(v_a_1580_);
v_r_1583_ = lean_box(v_res_1582_);
return v_r_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3(lean_object* v_00_u03b2_1584_, lean_object* v_data_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_data_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4(lean_object* v_00_u03b2_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1588_, v_b_1589_, v_x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6(lean_object* v_00_u03b2_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_x_1593_, v_x_1594_, v_x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(lean_object* v_00_u03b2_1597_, lean_object* v_a_1598_, lean_object* v_x_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1598_, v_x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1601_, lean_object* v_a_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(v_00_u03b2_1601_, v_a_1602_, v_x_1603_);
lean_dec(v_x_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1605_, lean_object* v_i_1606_, lean_object* v_source_1607_, lean_object* v_target_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v_i_1606_, v_source_1607_, v_target_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1610_, lean_object* v_x_1611_, size_t v_x_1612_, size_t v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1611_, v_x_1612_, v_x_1613_, v_x_1614_, v_x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
size_t v_x_12272__boxed_1623_; size_t v_x_12273__boxed_1624_; lean_object* v_res_1625_; 
v_x_12272__boxed_1623_ = lean_unbox_usize(v_x_1619_);
lean_dec(v_x_1619_);
v_x_12273__boxed_1624_ = lean_unbox_usize(v_x_1620_);
lean_dec(v_x_1620_);
v_res_1625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(v_00_u03b2_1617_, v_x_1618_, v_x_12272__boxed_1623_, v_x_12273__boxed_1624_, v_x_1621_, v_x_1622_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_x_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1630_, lean_object* v_n_1631_, lean_object* v_k_1632_, lean_object* v_v_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v_n_1631_, v_k_1632_, v_v_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1635_, size_t v_depth_1636_, lean_object* v_keys_1637_, lean_object* v_vals_1638_, lean_object* v_heq_1639_, lean_object* v_i_1640_, lean_object* v_entries_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_1636_, v_keys_1637_, v_vals_1638_, v_i_1640_, v_entries_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_depth_1644_, lean_object* v_keys_1645_, lean_object* v_vals_1646_, lean_object* v_heq_1647_, lean_object* v_i_1648_, lean_object* v_entries_1649_){
_start:
{
size_t v_depth_boxed_1650_; lean_object* v_res_1651_; 
v_depth_boxed_1650_ = lean_unbox_usize(v_depth_1644_);
lean_dec(v_depth_1644_);
v_res_1651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(v_00_u03b2_1643_, v_depth_boxed_1650_, v_keys_1645_, v_vals_1646_, v_heq_1647_, v_i_1648_, v_entries_1649_);
lean_dec_ref(v_vals_1646_);
lean_dec_ref(v_keys_1645_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15(lean_object* v_00_u03b2_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_x_1653_, v_x_1654_, v_x_1655_, v_x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1(){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1699_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
v___x_1701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15));
v___x_1702_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed), 10, 0);
v___x_1703_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1699_, v___x_1700_, v___x_1701_, v___x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___boxed(lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
return v_res_1705_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_DSimp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
