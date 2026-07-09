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
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*);
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
lean_dec(v___y_252_);
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
lean_inc(v___y_330_);
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
lean_inc(v___y_330_);
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
lean_dec(v_a_372_);
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
v___x_397_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_383_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
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
v___x_403_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_399_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
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
lean_dec(v___y_421_);
lean_dec(v___y_420_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(lean_object* v___f_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
lean_inc_ref(v___y_432_);
v___x_443_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_432_, v___y_437_);
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
lean_dec(v___y_434_);
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
lean_dec(v___y_434_);
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
lean_dec(v___y_434_);
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
lean_dec(v_a_539_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(lean_object* v_variantName_577_, lean_object* v_args_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
uint8_t v___x_588_; 
v___x_588_ = l_Lean_Name_isAnonymous(v_variantName_577_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v_env_590_; lean_object* v___x_591_; 
v___x_589_ = lean_st_ref_get(v_a_586_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_589_);
v___x_591_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_590_, v_variantName_577_);
if (lean_obj_tag(v___x_591_) == 1)
{
lean_object* v_val_592_; lean_object* v_pre_x3f_593_; lean_object* v_post_x3f_594_; lean_object* v_config_595_; lean_object* v___x_596_; 
lean_dec(v_variantName_577_);
v_val_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v___x_591_, 1);
v_pre_x3f_593_ = lean_ctor_get(v_val_592_, 0);
lean_inc(v_pre_x3f_593_);
v_post_x3f_594_ = lean_ctor_get(v_val_592_, 1);
lean_inc(v_post_x3f_594_);
v_config_595_ = lean_ctor_get(v_val_592_, 2);
lean_inc(v_config_595_);
lean_dec(v_val_592_);
v___x_596_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_pre_x3f_593_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_post_x3f_594_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_609_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_609_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_609_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_603_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed), 13, 2);
lean_closure_set(v___x_603_, 0, v_a_597_);
lean_closure_set(v___x_603_, 1, v_args_578_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_a_599_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_config_595_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_605_);
v___x_607_ = v___x_601_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_597_);
lean_dec(v_config_595_);
lean_dec_ref(v_args_578_);
v_a_610_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_598_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_598_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_config_595_);
lean_dec(v_post_x3f_594_);
lean_dec_ref(v_args_578_);
v_a_618_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_596_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_596_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v___x_591_);
lean_dec_ref(v_args_578_);
v___x_626_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1);
v___x_627_ = l_Lean_MessageData_ofName(v_variantName_577_);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__5);
v___x_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_630_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
return v___x_631_;
}
}
else
{
lean_object* v___x_632_; lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_variantName_577_);
v___x_632_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_578_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_642_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = lean_unsigned_to_nat(100000u);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_a_633_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_638_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___boxed(lean_object* v_variantName_643_, lean_object* v_args_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v_variantName_643_, v_args_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_654_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_box(0);
v___x_656_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg(){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0);
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___boxed(lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(lean_object* v_00_u03b1_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___boxed(lean_object* v_00_u03b1_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(v_00_u03b1_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
v___x_696_ = lean_apply_10(v_x_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, lean_box(0));
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed(lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(lean_object* v_mvarId_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___f_721_; lean_object* v___x_722_; 
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc(v___y_713_);
lean_inc_ref(v___y_712_);
lean_inc(v___y_711_);
v___f_721_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_721_, 0, v_x_710_);
lean_closure_set(v___f_721_, 1, v___y_711_);
lean_closure_set(v___f_721_, 2, v___y_712_);
lean_closure_set(v___f_721_, 3, v___y_713_);
lean_closure_set(v___f_721_, 4, v___y_714_);
lean_closure_set(v___f_721_, 5, v___y_715_);
v___x_722_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_709_, v___f_721_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_722_) == 0)
{
return v___x_722_;
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___boxed(lean_object* v_mvarId_731_, lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_731_, v_x_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(lean_object* v_00_u03b1_744_, lean_object* v_mvarId_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed(lean_object* v_00_u03b1_758_, lean_object* v_mvarId_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(v_00_u03b1_758_, v_mvarId_759_, v_x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(lean_object* v_mvarId_772_, lean_object* v_fst_773_, lean_object* v_snd_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_MVarId_getType(v_mvarId_772_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_788_, 0, v_a_787_);
v___x_789_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_788_, v_fst_773_, v_snd_774_, v___y_775_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
return v___x_789_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v___y_775_);
lean_dec(v_snd_774_);
lean_dec_ref(v_fst_773_);
v_a_790_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_786_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed(lean_object* v_mvarId_798_, lean_object* v_fst_799_, lean_object* v_snd_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(v_mvarId_798_, v_fst_799_, v_snd_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
lean_object* v_ks_817_; lean_object* v_vs_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_842_; 
v_ks_817_ = lean_ctor_get(v_x_813_, 0);
v_vs_818_ = lean_ctor_get(v_x_813_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_813_);
if (v_isSharedCheck_842_ == 0)
{
v___x_820_ = v_x_813_;
v_isShared_821_ = v_isSharedCheck_842_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_vs_818_);
lean_inc(v_ks_817_);
lean_dec(v_x_813_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_842_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_array_get_size(v_ks_817_);
v___x_823_ = lean_nat_dec_lt(v_x_814_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec(v_x_814_);
v___x_824_ = lean_array_push(v_ks_817_, v_x_815_);
v___x_825_ = lean_array_push(v_vs_818_, v_x_816_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_825_);
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_827_ = v___x_820_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v_k_x27_829_; uint8_t v___x_830_; 
v_k_x27_829_ = lean_array_fget_borrowed(v_ks_817_, v_x_814_);
v___x_830_ = l_Lean_instBEqMVarId_beq(v_x_815_, v_k_x27_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_832_; 
if (v_isShared_821_ == 0)
{
v___x_832_ = v___x_820_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_ks_817_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_vs_818_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_x_814_, v___x_833_);
lean_dec(v_x_814_);
v_x_813_ = v___x_832_;
v_x_814_ = v___x_834_;
goto _start;
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = lean_array_fset(v_ks_817_, v_x_814_, v_x_815_);
v___x_838_ = lean_array_fset(v_vs_818_, v_x_814_, v_x_816_);
lean_dec(v_x_814_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_838_);
lean_ctor_set(v___x_820_, 0, v___x_837_);
v___x_840_ = v___x_820_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(lean_object* v_n_843_, lean_object* v_k_844_, lean_object* v_v_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_n_843_, v___x_846_, v_k_844_, v_v_845_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(lean_object* v_x_849_, size_t v_x_850_, size_t v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v_es_854_; size_t v___x_855_; size_t v___x_856_; lean_object* v_j_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_es_854_ = lean_ctor_get(v_x_849_, 0);
v___x_855_ = ((size_t)31ULL);
v___x_856_ = lean_usize_land(v_x_850_, v___x_855_);
v_j_857_ = lean_usize_to_nat(v___x_856_);
v___x_858_ = lean_array_get_size(v_es_854_);
v___x_859_ = lean_nat_dec_lt(v_j_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_dec(v_j_857_);
lean_dec(v_x_853_);
lean_dec(v_x_852_);
return v_x_849_;
}
else
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_898_; 
lean_inc_ref(v_es_854_);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_x_849_, 0);
lean_dec(v_unused_899_);
v___x_861_ = v_x_849_;
v_isShared_862_ = v_isSharedCheck_898_;
goto v_resetjp_860_;
}
else
{
lean_dec(v_x_849_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_898_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_v_863_; lean_object* v___x_864_; lean_object* v_xs_x27_865_; lean_object* v___y_867_; 
v_v_863_ = lean_array_fget(v_es_854_, v_j_857_);
v___x_864_ = lean_box(0);
v_xs_x27_865_ = lean_array_fset(v_es_854_, v_j_857_, v___x_864_);
switch(lean_obj_tag(v_v_863_))
{
case 0:
{
lean_object* v_key_872_; lean_object* v_val_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_883_; 
v_key_872_ = lean_ctor_get(v_v_863_, 0);
v_val_873_ = lean_ctor_get(v_v_863_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_v_863_);
if (v_isSharedCheck_883_ == 0)
{
v___x_875_ = v_v_863_;
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_val_873_);
lean_inc(v_key_872_);
lean_dec(v_v_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_instBEqMVarId_beq(v_x_852_, v_key_872_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_del_object(v___x_875_);
v___x_878_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_872_, v_val_873_, v_x_852_, v_x_853_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
v___y_867_ = v___x_879_;
goto v___jp_866_;
}
else
{
lean_object* v___x_881_; 
lean_dec(v_val_873_);
lean_dec(v_key_872_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_x_853_);
lean_ctor_set(v___x_875_, 0, v_x_852_);
v___x_881_ = v___x_875_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_x_852_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_x_853_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
v___y_867_ = v___x_881_;
goto v___jp_866_;
}
}
}
}
case 1:
{
lean_object* v_node_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_896_; 
v_node_884_ = lean_ctor_get(v_v_863_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_v_863_);
if (v_isSharedCheck_896_ == 0)
{
v___x_886_ = v_v_863_;
v_isShared_887_ = v_isSharedCheck_896_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_node_884_);
lean_dec(v_v_863_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_896_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_888_ = ((size_t)5ULL);
v___x_889_ = lean_usize_shift_right(v_x_850_, v___x_888_);
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_add(v_x_851_, v___x_890_);
v___x_892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_node_884_, v___x_889_, v___x_891_, v_x_852_, v_x_853_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_892_);
v___x_894_ = v___x_886_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
v___y_867_ = v___x_894_;
goto v___jp_866_;
}
}
}
default: 
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_x_852_);
lean_ctor_set(v___x_897_, 1, v_x_853_);
v___y_867_ = v___x_897_;
goto v___jp_866_;
}
}
v___jp_866_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_array_fset(v_xs_x27_865_, v_j_857_, v___y_867_);
lean_dec(v_j_857_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
else
{
lean_object* v_ks_900_; lean_object* v_vs_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_921_; 
v_ks_900_ = lean_ctor_get(v_x_849_, 0);
v_vs_901_ = lean_ctor_get(v_x_849_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_921_ == 0)
{
v___x_903_ = v_x_849_;
v_isShared_904_ = v_isSharedCheck_921_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_vs_901_);
lean_inc(v_ks_900_);
lean_dec(v_x_849_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_921_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_ks_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_vs_901_);
v___x_906_ = v_reuseFailAlloc_920_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v_newNode_907_; uint8_t v___y_909_; size_t v___x_915_; uint8_t v___x_916_; 
v_newNode_907_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v___x_906_, v_x_852_, v_x_853_);
v___x_915_ = ((size_t)7ULL);
v___x_916_ = lean_usize_dec_le(v___x_915_, v_x_851_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_907_);
v___x_918_ = lean_unsigned_to_nat(4u);
v___x_919_ = lean_nat_dec_lt(v___x_917_, v___x_918_);
lean_dec(v___x_917_);
v___y_909_ = v___x_919_;
goto v___jp_908_;
}
else
{
v___y_909_ = v___x_916_;
goto v___jp_908_;
}
v___jp_908_:
{
if (v___y_909_ == 0)
{
lean_object* v_ks_910_; lean_object* v_vs_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_ks_910_ = lean_ctor_get(v_newNode_907_, 0);
lean_inc_ref(v_ks_910_);
v_vs_911_ = lean_ctor_get(v_newNode_907_, 1);
lean_inc_ref(v_vs_911_);
lean_dec_ref(v_newNode_907_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0);
v___x_914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_x_851_, v_ks_910_, v_vs_911_, v___x_912_, v___x_913_);
lean_dec_ref(v_vs_911_);
lean_dec_ref(v_ks_910_);
return v___x_914_;
}
else
{
return v_newNode_907_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(size_t v_depth_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_i_925_, lean_object* v_entries_926_){
_start:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_array_get_size(v_keys_923_);
v___x_928_ = lean_nat_dec_lt(v_i_925_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v_i_925_);
return v_entries_926_;
}
else
{
lean_object* v_k_929_; lean_object* v_v_930_; uint64_t v___x_931_; size_t v_h_932_; size_t v___x_933_; lean_object* v___x_934_; size_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v_h_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_k_929_ = lean_array_fget_borrowed(v_keys_923_, v_i_925_);
v_v_930_ = lean_array_fget_borrowed(v_vals_924_, v_i_925_);
v___x_931_ = l_Lean_instHashableMVarId_hash(v_k_929_);
v_h_932_ = lean_uint64_to_usize(v___x_931_);
v___x_933_ = ((size_t)5ULL);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_sub(v_depth_922_, v___x_935_);
v___x_937_ = lean_usize_mul(v___x_933_, v___x_936_);
v_h_938_ = lean_usize_shift_right(v_h_932_, v___x_937_);
v___x_939_ = lean_nat_add(v_i_925_, v___x_934_);
lean_dec(v_i_925_);
lean_inc(v_v_930_);
lean_inc(v_k_929_);
v___x_940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_entries_926_, v_h_938_, v_depth_922_, v_k_929_, v_v_930_);
v_i_925_ = v___x_939_;
v_entries_926_ = v___x_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_942_, lean_object* v_keys_943_, lean_object* v_vals_944_, lean_object* v_i_945_, lean_object* v_entries_946_){
_start:
{
size_t v_depth_boxed_947_; lean_object* v_res_948_; 
v_depth_boxed_947_ = lean_unbox_usize(v_depth_942_);
lean_dec(v_depth_942_);
v_res_948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_boxed_947_, v_keys_943_, v_vals_944_, v_i_945_, v_entries_946_);
lean_dec_ref(v_vals_944_);
lean_dec_ref(v_keys_943_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
size_t v_x_11104__boxed_954_; size_t v_x_11105__boxed_955_; lean_object* v_res_956_; 
v_x_11104__boxed_954_ = lean_unbox_usize(v_x_950_);
lean_dec(v_x_950_);
v_x_11105__boxed_955_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_949_, v_x_11104__boxed_954_, v_x_11105__boxed_955_, v_x_952_, v_x_953_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
uint64_t v___x_960_; size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_960_ = l_Lean_instHashableMVarId_hash(v_x_958_);
v___x_961_ = lean_uint64_to_usize(v___x_960_);
v___x_962_ = ((size_t)1ULL);
v___x_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_957_, v___x_961_, v___x_962_, v_x_958_, v_x_959_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object* v_mvarId_964_, lean_object* v_val_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v_mctx_969_; lean_object* v_cache_970_; lean_object* v_zetaDeltaFVarIds_971_; lean_object* v_postponed_972_; lean_object* v_diag_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1001_; 
v___x_968_ = lean_st_ref_take(v___y_966_);
v_mctx_969_ = lean_ctor_get(v___x_968_, 0);
v_cache_970_ = lean_ctor_get(v___x_968_, 1);
v_zetaDeltaFVarIds_971_ = lean_ctor_get(v___x_968_, 2);
v_postponed_972_ = lean_ctor_get(v___x_968_, 3);
v_diag_973_ = lean_ctor_get(v___x_968_, 4);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_975_ = v___x_968_;
v_isShared_976_ = v_isSharedCheck_1001_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_diag_973_);
lean_inc(v_postponed_972_);
lean_inc(v_zetaDeltaFVarIds_971_);
lean_inc(v_cache_970_);
lean_inc(v_mctx_969_);
lean_dec(v___x_968_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1001_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_depth_977_; lean_object* v_levelAssignDepth_978_; lean_object* v_lmvarCounter_979_; lean_object* v_mvarCounter_980_; lean_object* v_lDecls_981_; lean_object* v_decls_982_; lean_object* v_userNames_983_; lean_object* v_lAssignment_984_; lean_object* v_eAssignment_985_; lean_object* v_dAssignment_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v_depth_977_ = lean_ctor_get(v_mctx_969_, 0);
v_levelAssignDepth_978_ = lean_ctor_get(v_mctx_969_, 1);
v_lmvarCounter_979_ = lean_ctor_get(v_mctx_969_, 2);
v_mvarCounter_980_ = lean_ctor_get(v_mctx_969_, 3);
v_lDecls_981_ = lean_ctor_get(v_mctx_969_, 4);
v_decls_982_ = lean_ctor_get(v_mctx_969_, 5);
v_userNames_983_ = lean_ctor_get(v_mctx_969_, 6);
v_lAssignment_984_ = lean_ctor_get(v_mctx_969_, 7);
v_eAssignment_985_ = lean_ctor_get(v_mctx_969_, 8);
v_dAssignment_986_ = lean_ctor_get(v_mctx_969_, 9);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_mctx_969_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_988_ = v_mctx_969_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_dAssignment_986_);
lean_inc(v_eAssignment_985_);
lean_inc(v_lAssignment_984_);
lean_inc(v_userNames_983_);
lean_inc(v_decls_982_);
lean_inc(v_lDecls_981_);
lean_inc(v_mvarCounter_980_);
lean_inc(v_lmvarCounter_979_);
lean_inc(v_levelAssignDepth_978_);
lean_inc(v_depth_977_);
lean_dec(v_mctx_969_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_eAssignment_985_, v_mvarId_964_, v_val_965_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 8, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_depth_977_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_levelAssignDepth_978_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_lmvarCounter_979_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_mvarCounter_980_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_lDecls_981_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_decls_982_);
lean_ctor_set(v_reuseFailAlloc_999_, 6, v_userNames_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 7, v_lAssignment_984_);
lean_ctor_set(v_reuseFailAlloc_999_, 8, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 9, v_dAssignment_986_);
v___x_992_ = v_reuseFailAlloc_999_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_992_);
v___x_994_ = v___x_975_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_cache_970_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_zetaDeltaFVarIds_971_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_postponed_972_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_diag_973_);
v___x_994_ = v_reuseFailAlloc_998_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_st_ref_set(v___y_966_, v___x_994_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object* v_mvarId_1002_, lean_object* v_val_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1002_, v_val_1003_, v___y_1004_);
lean_dec(v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
uint8_t v___x_1009_; 
v___x_1009_ = 0;
return v___x_1009_;
}
else
{
lean_object* v_key_1010_; lean_object* v_tail_1011_; uint8_t v___x_1012_; 
v_key_1010_ = lean_ctor_get(v_x_1008_, 0);
v_tail_1011_ = lean_ctor_get(v_x_1008_, 2);
v___x_1012_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1010_, v_a_1007_);
if (v___x_1012_ == 0)
{
v_x_1008_ = v_tail_1011_;
goto _start;
}
else
{
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg___boxed(lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1014_, v_x_1015_);
lean_dec(v_x_1015_);
lean_dec_ref(v_a_1014_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(lean_object* v_a_1018_, lean_object* v_b_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_dec(v_b_1019_);
lean_dec_ref(v_a_1018_);
return v_x_1020_;
}
else
{
lean_object* v_key_1021_; lean_object* v_value_1022_; lean_object* v_tail_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1035_; 
v_key_1021_ = lean_ctor_get(v_x_1020_, 0);
v_value_1022_ = lean_ctor_get(v_x_1020_, 1);
v_tail_1023_ = lean_ctor_get(v_x_1020_, 2);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_1020_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1025_ = v_x_1020_;
v_isShared_1026_ = v_isSharedCheck_1035_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_tail_1023_);
lean_inc(v_value_1022_);
lean_inc(v_key_1021_);
lean_dec(v_x_1020_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1035_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1021_, v_a_1018_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1018_, v_b_1019_, v_tail_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 2, v___x_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_key_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_value_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v___x_1033_; 
lean_dec(v_value_1022_);
lean_dec(v_key_1021_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v_b_1019_);
lean_ctor_set(v___x_1025_, 0, v_a_1018_);
v___x_1033_ = v___x_1025_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1018_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_b_1019_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_tail_1023_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
return v_x_1036_;
}
else
{
lean_object* v_key_1038_; lean_object* v_value_1039_; lean_object* v_tail_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1063_; 
v_key_1038_ = lean_ctor_get(v_x_1037_, 0);
v_value_1039_ = lean_ctor_get(v_x_1037_, 1);
v_tail_1040_ = lean_ctor_get(v_x_1037_, 2);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_x_1037_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1042_ = v_x_1037_;
v_isShared_1043_ = v_isSharedCheck_1063_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_tail_1040_);
lean_inc(v_value_1039_);
lean_inc(v_key_1038_);
lean_dec(v_x_1037_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1063_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v_fold_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1044_ = lean_array_get_size(v_x_1036_);
v___x_1045_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_key_1038_);
v___x_1046_ = 32ULL;
v___x_1047_ = lean_uint64_shift_right(v___x_1045_, v___x_1046_);
v_fold_1048_ = lean_uint64_xor(v___x_1045_, v___x_1047_);
v___x_1049_ = 16ULL;
v___x_1050_ = lean_uint64_shift_right(v_fold_1048_, v___x_1049_);
v___x_1051_ = lean_uint64_xor(v_fold_1048_, v___x_1050_);
v___x_1052_ = lean_uint64_to_usize(v___x_1051_);
v___x_1053_ = lean_usize_of_nat(v___x_1044_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_sub(v___x_1053_, v___x_1054_);
v___x_1056_ = lean_usize_land(v___x_1052_, v___x_1055_);
v___x_1057_ = lean_array_uget_borrowed(v_x_1036_, v___x_1056_);
lean_inc(v___x_1057_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 2, v___x_1057_);
v___x_1059_ = v___x_1042_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_key_1038_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_value_1039_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_array_uset(v_x_1036_, v___x_1056_, v___x_1059_);
v_x_1036_ = v___x_1060_;
v_x_1037_ = v_tail_1040_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1064_, lean_object* v_source_1065_, lean_object* v_target_1066_){
_start:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_array_get_size(v_source_1065_);
v___x_1068_ = lean_nat_dec_lt(v_i_1064_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v_source_1065_);
lean_dec(v_i_1064_);
return v_target_1066_;
}
else
{
lean_object* v_es_1069_; lean_object* v___x_1070_; lean_object* v_source_1071_; lean_object* v_target_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_es_1069_ = lean_array_fget(v_source_1065_, v_i_1064_);
v___x_1070_ = lean_box(0);
v_source_1071_ = lean_array_fset(v_source_1065_, v_i_1064_, v___x_1070_);
v_target_1072_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1066_, v_es_1069_);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_nat_add(v_i_1064_, v___x_1073_);
lean_dec(v_i_1064_);
v_i_1064_ = v___x_1074_;
v_source_1065_ = v_source_1071_;
v_target_1066_ = v_target_1072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(lean_object* v_data_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_nbuckets_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1077_ = lean_array_get_size(v_data_1076_);
v___x_1078_ = lean_unsigned_to_nat(2u);
v_nbuckets_1079_ = lean_nat_mul(v___x_1077_, v___x_1078_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_mk_array(v_nbuckets_1079_, v___x_1081_);
v___x_1083_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v___x_1080_, v_data_1076_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object* v_m_1084_, lean_object* v_a_1085_, lean_object* v_b_1086_){
_start:
{
lean_object* v_size_1087_; lean_object* v_buckets_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1131_; 
v_size_1087_ = lean_ctor_get(v_m_1084_, 0);
v_buckets_1088_ = lean_ctor_get(v_m_1084_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_m_1084_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1090_ = v_m_1084_;
v_isShared_1091_ = v_isSharedCheck_1131_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_buckets_1088_);
lean_inc(v_size_1087_);
lean_dec(v_m_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1131_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v_fold_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; lean_object* v_bkt_1105_; uint8_t v___x_1106_; 
v___x_1092_ = lean_array_get_size(v_buckets_1088_);
v___x_1093_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1085_);
v___x_1094_ = 32ULL;
v___x_1095_ = lean_uint64_shift_right(v___x_1093_, v___x_1094_);
v_fold_1096_ = lean_uint64_xor(v___x_1093_, v___x_1095_);
v___x_1097_ = 16ULL;
v___x_1098_ = lean_uint64_shift_right(v_fold_1096_, v___x_1097_);
v___x_1099_ = lean_uint64_xor(v_fold_1096_, v___x_1098_);
v___x_1100_ = lean_uint64_to_usize(v___x_1099_);
v___x_1101_ = lean_usize_of_nat(v___x_1092_);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_sub(v___x_1101_, v___x_1102_);
v___x_1104_ = lean_usize_land(v___x_1100_, v___x_1103_);
v_bkt_1105_ = lean_array_uget_borrowed(v_buckets_1088_, v___x_1104_);
v___x_1106_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1085_, v_bkt_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v_size_x27_1108_; lean_object* v___x_1109_; lean_object* v_buckets_x27_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
v_size_x27_1108_ = lean_nat_add(v_size_1087_, v___x_1107_);
lean_dec(v_size_1087_);
lean_inc(v_bkt_1105_);
v___x_1109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1109_, 0, v_a_1085_);
lean_ctor_set(v___x_1109_, 1, v_b_1086_);
lean_ctor_set(v___x_1109_, 2, v_bkt_1105_);
v_buckets_x27_1110_ = lean_array_uset(v_buckets_1088_, v___x_1104_, v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(4u);
v___x_1112_ = lean_nat_mul(v_size_x27_1108_, v___x_1111_);
v___x_1113_ = lean_unsigned_to_nat(3u);
v___x_1114_ = lean_nat_div(v___x_1112_, v___x_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_array_get_size(v_buckets_x27_1110_);
v___x_1116_ = lean_nat_dec_le(v___x_1114_, v___x_1115_);
lean_dec(v___x_1114_);
if (v___x_1116_ == 0)
{
lean_object* v_val_1117_; lean_object* v___x_1119_; 
v_val_1117_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_buckets_x27_1110_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_val_1117_);
lean_ctor_set(v___x_1090_, 0, v_size_x27_1108_);
v___x_1119_ = v___x_1090_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_size_x27_1108_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_val_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v___x_1122_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_buckets_x27_1110_);
lean_ctor_set(v___x_1090_, 0, v_size_x27_1108_);
v___x_1122_ = v___x_1090_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_size_x27_1108_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_buckets_x27_1110_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v_buckets_x27_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_inc(v_bkt_1105_);
v___x_1124_ = lean_box(0);
v_buckets_x27_1125_ = lean_array_uset(v_buckets_1088_, v___x_1104_, v___x_1124_);
v___x_1126_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1085_, v_b_1086_, v_bkt_1105_);
v___x_1127_ = lean_array_uset(v_buckets_x27_1125_, v___x_1104_, v___x_1126_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v___x_1127_);
v___x_1129_ = v___x_1090_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_size_1087_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(lean_object* v_a_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v_key_1135_; lean_object* v_value_1136_; lean_object* v_tail_1137_; uint8_t v___x_1138_; 
v_key_1135_ = lean_ctor_get(v_x_1133_, 0);
v_value_1136_ = lean_ctor_get(v_x_1133_, 1);
v_tail_1137_ = lean_ctor_get(v_x_1133_, 2);
v___x_1138_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1135_, v_a_1132_);
if (v___x_1138_ == 0)
{
v_x_1133_ = v_tail_1137_;
goto _start;
}
else
{
lean_object* v___x_1140_; 
lean_inc(v_value_1136_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_value_1136_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg___boxed(lean_object* v_a_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1141_, v_x_1142_);
lean_dec(v_x_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_buckets_1146_; lean_object* v___x_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v_fold_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_buckets_1146_ = lean_ctor_get(v_m_1144_, 1);
v___x_1147_ = lean_array_get_size(v_buckets_1146_);
v___x_1148_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1145_);
v___x_1149_ = 32ULL;
v___x_1150_ = lean_uint64_shift_right(v___x_1148_, v___x_1149_);
v_fold_1151_ = lean_uint64_xor(v___x_1148_, v___x_1150_);
v___x_1152_ = 16ULL;
v___x_1153_ = lean_uint64_shift_right(v_fold_1151_, v___x_1152_);
v___x_1154_ = lean_uint64_xor(v_fold_1151_, v___x_1153_);
v___x_1155_ = lean_uint64_to_usize(v___x_1154_);
v___x_1156_ = lean_usize_of_nat(v___x_1147_);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_sub(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_usize_land(v___x_1155_, v___x_1158_);
v___x_1160_ = lean_array_uget_borrowed(v_buckets_1146_, v___x_1159_);
v___x_1161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1145_, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object* v_m_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1162_, v_a_1163_);
lean_dec_ref(v_a_1163_);
lean_dec_ref(v_m_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(uint8_t v___x_1165_, uint8_t v___x_1166_, lean_object* v_as_1167_, size_t v_i_1168_, size_t v_stop_1169_, lean_object* v_b_1170_){
_start:
{
lean_object* v___y_1172_; uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_eq(v_i_1168_, v_stop_1169_);
if (v___x_1176_ == 0)
{
lean_object* v_fst_1177_; uint8_t v___x_1178_; 
v_fst_1177_ = lean_ctor_get(v_b_1170_, 0);
v___x_1178_ = lean_unbox(v_fst_1177_);
if (v___x_1178_ == 0)
{
lean_object* v_snd_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
v_snd_1179_ = lean_ctor_get(v_b_1170_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_b_1170_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_b_1170_, 0);
lean_dec(v_unused_1188_);
v___x_1181_ = v_b_1170_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_snd_1179_);
lean_dec(v_b_1170_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_box(v___x_1165_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1179_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
v___y_1172_ = v___x_1185_;
goto v___jp_1171_;
}
}
}
else
{
lean_object* v_snd_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1199_; 
v_snd_1189_ = lean_ctor_get(v_b_1170_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_b_1170_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_b_1170_, 0);
lean_dec(v_unused_1200_);
v___x_1191_ = v_b_1170_;
v_isShared_1192_ = v_isSharedCheck_1199_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_snd_1189_);
lean_dec(v_b_1170_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1199_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1193_ = lean_array_uget_borrowed(v_as_1167_, v_i_1168_);
lean_inc(v___x_1193_);
v___x_1194_ = lean_array_push(v_snd_1189_, v___x_1193_);
v___x_1195_ = lean_box(v___x_1166_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1194_);
lean_ctor_set(v___x_1191_, 0, v___x_1195_);
v___x_1197_ = v___x_1191_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1194_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v___y_1172_ = v___x_1197_;
goto v___jp_1171_;
}
}
}
}
else
{
return v_b_1170_;
}
v___jp_1171_:
{
size_t v___x_1173_; size_t v___x_1174_; 
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1168_, v___x_1173_);
v_i_1168_ = v___x_1174_;
v_b_1170_ = v___y_1172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_as_1203_, lean_object* v_i_1204_, lean_object* v_stop_1205_, lean_object* v_b_1206_){
_start:
{
uint8_t v___x_11569__boxed_1207_; uint8_t v___x_11570__boxed_1208_; size_t v_i_boxed_1209_; size_t v_stop_boxed_1210_; lean_object* v_res_1211_; 
v___x_11569__boxed_1207_ = lean_unbox(v___x_1201_);
v___x_11570__boxed_1208_ = lean_unbox(v___x_1202_);
v_i_boxed_1209_ = lean_unbox_usize(v_i_1204_);
lean_dec(v_i_1204_);
v_stop_boxed_1210_ = lean_unbox_usize(v_stop_1205_);
lean_dec(v_stop_1205_);
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_11569__boxed_1207_, v___x_11570__boxed_1208_, v_as_1203_, v_i_boxed_1209_, v_stop_boxed_1210_, v_b_1206_);
lean_dec_ref(v_as_1203_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(size_t v_sz_1212_, size_t v_i_1213_, lean_object* v_bs_1214_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_lt(v_i_1213_, v_sz_1212_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_bs_1214_);
return v___x_1216_;
}
else
{
lean_object* v_v_1217_; lean_object* v___x_1218_; lean_object* v_bs_x27_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_v_1217_ = lean_array_uget(v_bs_1214_, v_i_1213_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v_bs_x27_1219_ = lean_array_uset(v_bs_1214_, v_i_1213_, v___x_1218_);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_add(v_i_1213_, v___x_1220_);
v___x_1222_ = lean_array_uset(v_bs_x27_1219_, v_i_1213_, v_v_1217_);
v_i_1213_ = v___x_1221_;
v_bs_1214_ = v___x_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object* v_sz_1224_, lean_object* v_i_1225_, lean_object* v_bs_1226_){
_start:
{
size_t v_sz_boxed_1227_; size_t v_i_boxed_1228_; lean_object* v_res_1229_; 
v_sz_boxed_1227_ = lean_unbox_usize(v_sz_1224_);
lean_dec(v_sz_1224_);
v_i_boxed_1228_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_boxed_1227_, v_i_boxed_1228_, v_bs_1226_);
return v_res_1229_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0));
v___x_1232_ = l_Lean_stringToMessageData(v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4));
v___x_1240_ = l_Lean_mkConst(v___x_1239_, v___x_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(lean_object* v_stx_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_1261_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1501_; 
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1502_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1501_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1501_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
lean_inc(v_stx_1260_);
v___x_1398_ = l_Lean_Syntax_isOfKind(v_stx_1260_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_del_object(v___x_1395_);
lean_dec(v_stx_1260_);
v___x_1399_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1430_; lean_object* v_args_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___x_1458_; lean_object* v_variantId_x3f_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1492_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1458_);
v___x_1493_ = l_Lean_Syntax_isNone(v___x_1492_);
if (v___x_1493_ == 0)
{
uint8_t v___x_1494_; 
lean_inc(v___x_1492_);
v___x_1494_ = l_Lean_Syntax_matchesNull(v___x_1492_, v___x_1458_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v___x_1492_);
lean_del_object(v___x_1395_);
lean_dec(v_stx_1260_);
v___x_1495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = l_Lean_Syntax_getArg(v___x_1492_, v___x_1400_);
lean_dec(v___x_1492_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 1);
lean_ctor_set(v___x_1395_, 0, v___x_1496_);
v___x_1498_ = v___x_1395_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v_variantId_x3f_1460_ = v___x_1498_;
v___y_1461_ = v___y_1261_;
v___y_1462_ = v___y_1262_;
v___y_1463_ = v___y_1263_;
v___y_1464_ = v___y_1264_;
v___y_1465_ = v___y_1265_;
v___y_1466_ = v___y_1266_;
v___y_1467_ = v___y_1267_;
v___y_1468_ = v___y_1268_;
goto v___jp_1459_;
}
}
}
else
{
lean_object* v___x_1500_; 
lean_dec(v___x_1492_);
lean_del_object(v___x_1395_);
v___x_1500_ = lean_box(0);
v_variantId_x3f_1460_ = v___x_1500_;
v___y_1461_ = v___y_1261_;
v___y_1462_ = v___y_1262_;
v___y_1463_ = v___y_1263_;
v___y_1464_ = v___y_1264_;
v___y_1465_ = v___y_1265_;
v___y_1466_ = v___y_1266_;
v___y_1467_ = v___y_1267_;
v___y_1468_ = v___y_1268_;
goto v___jp_1459_;
}
v___jp_1401_:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v___y_1406_, v___y_1402_, v___y_1410_, v___y_1404_, v___y_1405_, v___y_1407_, v___y_1409_, v___y_1408_, v___y_1403_);
lean_dec(v___y_1406_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v_cache_1415_; lean_object* v_dsimpState_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc_n(v_a_1413_, 2);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = lean_st_ref_get(v___y_1410_);
v_cache_1415_ = lean_ctor_get(v___x_1414_, 3);
lean_inc_ref(v_cache_1415_);
lean_dec(v___x_1414_);
v_dsimpState_1416_ = lean_ctor_get(v_cache_1415_, 3);
lean_inc_ref(v_dsimpState_1416_);
lean_dec_ref(v_cache_1415_);
lean_inc(v___y_1411_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___y_1411_);
lean_ctor_set(v___x_1417_, 1, v_a_1413_);
v___x_1418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_dsimpState_1416_, v___x_1417_);
lean_dec_ref(v_dsimpState_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14);
v___y_1271_ = v___y_1402_;
v___y_1272_ = v___y_1403_;
v___y_1273_ = v___y_1404_;
v___y_1274_ = v___y_1405_;
v___y_1275_ = v_a_1413_;
v___y_1276_ = v___x_1417_;
v___y_1277_ = v___y_1411_;
v___y_1278_ = v___y_1407_;
v___y_1279_ = v___y_1408_;
v___y_1280_ = v___y_1409_;
v___y_1281_ = v___y_1410_;
v___y_1282_ = v___x_1419_;
goto v___jp_1270_;
}
else
{
lean_object* v_val_1420_; 
v_val_1420_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v___x_1418_, 1);
v___y_1271_ = v___y_1402_;
v___y_1272_ = v___y_1403_;
v___y_1273_ = v___y_1404_;
v___y_1274_ = v___y_1405_;
v___y_1275_ = v_a_1413_;
v___y_1276_ = v___x_1417_;
v___y_1277_ = v___y_1411_;
v___y_1278_ = v___y_1407_;
v___y_1279_ = v___y_1408_;
v___y_1280_ = v___y_1409_;
v___y_1281_ = v___y_1410_;
v___y_1282_ = v_val_1420_;
goto v___jp_1270_;
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v___y_1411_);
v_a_1421_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1412_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1412_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
v___jp_1429_:
{
if (lean_obj_tag(v___y_1430_) == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_box(0);
v___y_1402_ = v___y_1432_;
v___y_1403_ = v___y_1439_;
v___y_1404_ = v___y_1434_;
v___y_1405_ = v___y_1435_;
v___y_1406_ = v_args_1431_;
v___y_1407_ = v___y_1436_;
v___y_1408_ = v___y_1438_;
v___y_1409_ = v___y_1437_;
v___y_1410_ = v___y_1433_;
v___y_1411_ = v___x_1440_;
goto v___jp_1401_;
}
else
{
lean_object* v_val_1441_; lean_object* v___x_1442_; 
v_val_1441_ = lean_ctor_get(v___y_1430_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___y_1430_, 1);
v___x_1442_ = l_Lean_TSyntax_getId(v_val_1441_);
lean_dec(v_val_1441_);
v___y_1402_ = v___y_1432_;
v___y_1403_ = v___y_1439_;
v___y_1404_ = v___y_1434_;
v___y_1405_ = v___y_1435_;
v___y_1406_ = v_args_1431_;
v___y_1407_ = v___y_1436_;
v___y_1408_ = v___y_1438_;
v___y_1409_ = v___y_1437_;
v___y_1410_ = v___y_1433_;
v___y_1411_ = v___x_1442_;
goto v___jp_1401_;
}
}
v___jp_1443_:
{
size_t v_sz_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v_sz_1454_ = lean_array_size(v___y_1453_);
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_1454_, v___x_1455_, v___y_1453_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1457_; 
lean_dec(v___y_1450_);
v___x_1457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1457_;
}
else
{
v___y_1430_ = v___y_1450_;
v_args_1431_ = v___x_1456_;
v___y_1432_ = v___y_1446_;
v___y_1433_ = v___y_1444_;
v___y_1434_ = v___y_1445_;
v___y_1435_ = v___y_1452_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___y_1451_;
v___y_1438_ = v___y_1448_;
v___y_1439_ = v___y_1449_;
goto v___jp_1429_;
}
}
v___jp_1459_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_unsigned_to_nat(2u);
v___x_1470_ = l_Lean_Syntax_getArg(v_stx_1260_, v___x_1469_);
lean_dec(v_stx_1260_);
v___x_1471_ = l_Lean_Syntax_isNone(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1470_);
v___x_1473_ = l_Lean_Syntax_matchesNull(v___x_1470_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_dec(v___x_1470_);
lean_dec(v_variantId_x3f_1460_);
v___x_1474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1475_ = l_Lean_Syntax_getArg(v___x_1470_, v___x_1458_);
lean_dec(v___x_1470_);
v___x_1476_ = l_Lean_Syntax_getArgs(v___x_1475_);
lean_dec(v___x_1475_);
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15));
v___x_1478_ = lean_array_get_size(v___x_1476_);
v___x_1479_ = lean_nat_dec_lt(v___x_1400_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec_ref(v___x_1476_);
v___y_1444_ = v___y_1462_;
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1461_;
v___y_1447_ = v___y_1465_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v_variantId_x3f_1460_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1464_;
v___y_1453_ = v___x_1477_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_box(v___x_1473_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1477_);
v___x_1482_ = lean_nat_dec_le(v___x_1478_, v___x_1478_);
if (v___x_1482_ == 0)
{
if (v___x_1479_ == 0)
{
lean_dec_ref_known(v___x_1481_, 2);
lean_dec_ref(v___x_1476_);
v___y_1444_ = v___y_1462_;
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1461_;
v___y_1447_ = v___y_1465_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v_variantId_x3f_1460_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1464_;
v___y_1453_ = v___x_1477_;
goto v___jp_1443_;
}
else
{
size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v_snd_1486_; 
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1478_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_1473_, v___x_1471_, v___x_1476_, v___x_1483_, v___x_1484_, v___x_1481_);
lean_dec_ref(v___x_1476_);
v_snd_1486_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_snd_1486_);
lean_dec_ref(v___x_1485_);
v___y_1444_ = v___y_1462_;
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1461_;
v___y_1447_ = v___y_1465_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v_variantId_x3f_1460_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1464_;
v___y_1453_ = v_snd_1486_;
goto v___jp_1443_;
}
}
else
{
size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; lean_object* v_snd_1490_; 
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1478_);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_1473_, v___x_1471_, v___x_1476_, v___x_1487_, v___x_1488_, v___x_1481_);
lean_dec_ref(v___x_1476_);
v_snd_1490_ = lean_ctor_get(v___x_1489_, 1);
lean_inc(v_snd_1490_);
lean_dec_ref(v___x_1489_);
v___y_1444_ = v___y_1462_;
v___y_1445_ = v___y_1463_;
v___y_1446_ = v___y_1461_;
v___y_1447_ = v___y_1465_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v_variantId_x3f_1460_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1464_;
v___y_1453_ = v_snd_1490_;
goto v___jp_1443_;
}
}
}
}
else
{
lean_object* v___x_1491_; 
lean_dec(v___x_1470_);
v___x_1491_ = lean_box(0);
v___y_1430_ = v_variantId_x3f_1460_;
v_args_1431_ = v___x_1491_;
v___y_1432_ = v___y_1461_;
v___y_1433_ = v___y_1462_;
v___y_1434_ = v___y_1463_;
v___y_1435_ = v___y_1464_;
v___y_1436_ = v___y_1465_;
v___y_1437_ = v___y_1466_;
v___y_1438_ = v___y_1467_;
v___y_1439_ = v___y_1468_;
goto v___jp_1429_;
}
}
}
}
}
else
{
lean_dec(v_stx_1260_);
return v___x_1393_;
}
v___jp_1270_:
{
lean_object* v___x_1283_; 
v___x_1283_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v___y_1277_, v___y_1275_, v___y_1271_, v___y_1281_, v___y_1273_, v___y_1274_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1287_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v_fst_1285_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_fst_1285_);
v_snd_1286_ = lean_ctor_get(v_a_1284_, 1);
lean_inc(v_snd_1286_);
lean_dec(v_a_1284_);
v___x_1287_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1281_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_toGoalState_1289_; lean_object* v_mvarId_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1376_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_toGoalState_1289_ = lean_ctor_get(v_a_1288_, 0);
v_mvarId_1290_ = lean_ctor_get(v_a_1288_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1292_ = v_a_1288_;
v_isShared_1293_ = v_isSharedCheck_1376_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_mvarId_1290_);
lean_inc(v_toGoalState_1289_);
lean_dec(v_a_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1376_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc_n(v_mvarId_1290_, 2);
v___f_1294_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1294_, 0, v_mvarId_1290_);
lean_closure_set(v___f_1294_, 1, v_fst_1285_);
lean_closure_set(v___f_1294_, 2, v_snd_1286_);
lean_closure_set(v___f_1294_, 3, v___y_1282_);
v___x_1295_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed), 13, 3);
lean_closure_set(v___x_1295_, 0, lean_box(0));
lean_closure_set(v___x_1295_, 1, v_mvarId_1290_);
lean_closure_set(v___x_1295_, 2, v___f_1294_);
v___x_1296_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1295_, v___y_1271_, v___y_1281_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1367_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v_fst_1298_ = lean_ctor_get(v_a_1297_, 0);
v_snd_1299_ = lean_ctor_get(v_a_1297_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_a_1297_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1301_ = v_a_1297_;
v_isShared_1302_ = v_isSharedCheck_1367_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snd_1299_);
lean_inc(v_fst_1298_);
lean_dec(v_a_1297_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1367_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v_cache_1304_; lean_object* v_symState_1305_; lean_object* v_grindState_1306_; lean_object* v_goals_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1366_; 
v___x_1303_ = lean_st_ref_take(v___y_1281_);
v_cache_1304_ = lean_ctor_get(v___x_1303_, 3);
v_symState_1305_ = lean_ctor_get(v___x_1303_, 0);
v_grindState_1306_ = lean_ctor_get(v___x_1303_, 1);
v_goals_1307_ = lean_ctor_get(v___x_1303_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1309_ = v___x_1303_;
v_isShared_1310_ = v_isSharedCheck_1366_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_cache_1304_);
lean_inc(v_goals_1307_);
lean_inc(v_grindState_1306_);
lean_inc(v_symState_1305_);
lean_dec(v___x_1303_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1366_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_backwardRuleName_1311_; lean_object* v_backwardRuleSyntax_1312_; lean_object* v_simpState_1313_; lean_object* v_dsimpState_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1365_; 
v_backwardRuleName_1311_ = lean_ctor_get(v_cache_1304_, 0);
v_backwardRuleSyntax_1312_ = lean_ctor_get(v_cache_1304_, 1);
v_simpState_1313_ = lean_ctor_get(v_cache_1304_, 2);
v_dsimpState_1314_ = lean_ctor_get(v_cache_1304_, 3);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_cache_1304_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1316_ = v_cache_1304_;
v_isShared_1317_ = v_isSharedCheck_1365_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_dsimpState_1314_);
lean_inc(v_simpState_1313_);
lean_inc(v_backwardRuleSyntax_1312_);
lean_inc(v_backwardRuleName_1311_);
lean_dec(v_cache_1304_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1365_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_dsimpState_1314_, v___y_1276_, v_snd_1299_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 3, v___x_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_backwardRuleName_1311_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_backwardRuleSyntax_1312_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_simpState_1313_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1322_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 3, v___x_1320_);
v___x_1322_ = v___x_1309_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_symState_1305_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_grindState_1306_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_goals_1307_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_st_ref_set(v___y_1281_, v___x_1322_);
if (lean_obj_tag(v_fst_1298_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref_known(v_fst_1298_, 0);
lean_del_object(v___x_1301_);
lean_del_object(v___x_1292_);
lean_dec(v_mvarId_1290_);
lean_dec_ref(v_toGoalState_1289_);
v___x_1324_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1);
v___x_1325_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_1324_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
return v___x_1325_;
}
else
{
lean_object* v_e_x27_1326_; uint8_t v___x_1327_; 
v_e_x27_1326_ = lean_ctor_get(v_fst_1298_, 0);
lean_inc_ref_n(v_e_x27_1326_, 2);
lean_dec_ref_known(v_fst_1298_, 1);
v___x_1327_ = l_Lean_Expr_isTrue(v_e_x27_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_inc(v_mvarId_1290_);
v___x_1328_ = l_Lean_MVarId_getDecl(v_mvarId_1290_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_userName_1330_; lean_object* v___x_1331_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v_userName_1330_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_userName_1330_);
lean_dec(v_a_1329_);
v___x_1331_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_1326_, v_userName_1330_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc_n(v_a_1332_, 2);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1333_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1290_, v_a_1332_, v___y_1280_);
lean_dec_ref(v___x_1333_);
v___x_1334_ = l_Lean_Expr_mvarId_x21(v_a_1332_);
lean_dec(v_a_1332_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1334_);
v___x_1336_ = v___x_1292_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_toGoalState_1289_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(0);
if (v_isShared_1302_ == 0)
{
lean_ctor_set_tag(v___x_1301_, 1);
lean_ctor_set(v___x_1301_, 1, v___x_1337_);
lean_ctor_set(v___x_1301_, 0, v___x_1336_);
v___x_1339_ = v___x_1301_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1339_, v___y_1281_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_del_object(v___x_1301_);
lean_del_object(v___x_1292_);
lean_dec(v_mvarId_1290_);
lean_dec_ref(v_toGoalState_1289_);
v_a_1343_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1331_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1331_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_e_x27_1326_);
lean_del_object(v___x_1301_);
lean_del_object(v___x_1292_);
lean_dec(v_mvarId_1290_);
lean_dec_ref(v_toGoalState_1289_);
v_a_1351_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1328_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1328_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec_ref(v_e_x27_1326_);
lean_del_object(v___x_1301_);
lean_del_object(v___x_1292_);
lean_dec_ref(v_toGoalState_1289_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5);
v___x_1361_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1290_, v___x_1360_, v___y_1280_);
lean_dec_ref(v___x_1361_);
v___x_1362_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1359_, v___y_1281_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1272_);
return v___x_1362_;
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
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1292_);
lean_dec(v_mvarId_1290_);
lean_dec_ref(v_toGoalState_1289_);
lean_dec_ref(v___y_1276_);
v_a_1368_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1296_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1296_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_snd_1286_);
lean_dec(v_fst_1285_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v___y_1276_);
v_a_1377_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1287_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1287_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v___y_1282_);
lean_dec_ref(v___y_1276_);
v_a_1385_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1283_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1283_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed(lean_object* v_stx_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(v_stx_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(lean_object* v_stx_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___f_1524_; lean_object* v___x_1525_; 
v___f_1524_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1524_, 0, v_stx_1514_);
v___x_1525_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1524_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed(lean_object* v_stx_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(v_stx_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object* v_00_u03b2_1537_, lean_object* v_m_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_m_1538_, v_a_1539_, v_b_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object* v_mvarId_1542_, lean_object* v_val_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1542_, v_val_1543_, v___y_1549_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object* v_mvarId_1554_, lean_object* v_val_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(v_mvarId_1554_, v_val_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1567_, v_a_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(v_00_u03b2_1570_, v_m_1571_, v_a_1572_);
lean_dec_ref(v_a_1572_);
lean_dec_ref(v_m_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object* v_00_u03b2_1574_, lean_object* v_a_1575_, lean_object* v_x_1576_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1575_, v_x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1578_, lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(v_00_u03b2_1578_, v_a_1579_, v_x_1580_);
lean_dec(v_x_1580_);
lean_dec_ref(v_a_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3(lean_object* v_00_u03b2_1583_, lean_object* v_data_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_data_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4(lean_object* v_00_u03b2_1586_, lean_object* v_a_1587_, lean_object* v_b_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1587_, v_b_1588_, v_x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6(lean_object* v_00_u03b2_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_x_1592_, v_x_1593_, v_x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(lean_object* v_00_u03b2_1596_, lean_object* v_a_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1597_, v_x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1600_, lean_object* v_a_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(v_00_u03b2_1600_, v_a_1601_, v_x_1602_);
lean_dec(v_x_1602_);
lean_dec_ref(v_a_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1604_, lean_object* v_i_1605_, lean_object* v_source_1606_, lean_object* v_target_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v_i_1605_, v_source_1606_, v_target_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1609_, lean_object* v_x_1610_, size_t v_x_1611_, size_t v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1610_, v_x_1611_, v_x_1612_, v_x_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
size_t v_x_12272__boxed_1622_; size_t v_x_12273__boxed_1623_; lean_object* v_res_1624_; 
v_x_12272__boxed_1622_ = lean_unbox_usize(v_x_1618_);
lean_dec(v_x_1618_);
v_x_12273__boxed_1623_ = lean_unbox_usize(v_x_1619_);
lean_dec(v_x_1619_);
v_res_1624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(v_00_u03b2_1616_, v_x_1617_, v_x_12272__boxed_1622_, v_x_12273__boxed_1623_, v_x_1620_, v_x_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_x_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1629_, lean_object* v_n_1630_, lean_object* v_k_1631_, lean_object* v_v_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v_n_1630_, v_k_1631_, v_v_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1634_, size_t v_depth_1635_, lean_object* v_keys_1636_, lean_object* v_vals_1637_, lean_object* v_heq_1638_, lean_object* v_i_1639_, lean_object* v_entries_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_1635_, v_keys_1636_, v_vals_1637_, v_i_1639_, v_entries_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_depth_1643_, lean_object* v_keys_1644_, lean_object* v_vals_1645_, lean_object* v_heq_1646_, lean_object* v_i_1647_, lean_object* v_entries_1648_){
_start:
{
size_t v_depth_boxed_1649_; lean_object* v_res_1650_; 
v_depth_boxed_1649_ = lean_unbox_usize(v_depth_1643_);
lean_dec(v_depth_1643_);
v_res_1650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(v_00_u03b2_1642_, v_depth_boxed_1649_, v_keys_1644_, v_vals_1645_, v_heq_1646_, v_i_1647_, v_entries_1648_);
lean_dec_ref(v_vals_1645_);
lean_dec_ref(v_keys_1644_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15(lean_object* v_00_u03b2_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_x_1652_, v_x_1653_, v_x_1654_, v_x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1(){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1698_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
v___x_1700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15));
v___x_1701_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed), 10, 0);
v___x_1702_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1698_, v___x_1699_, v___x_1700_, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___boxed(lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
return v_res_1704_;
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
