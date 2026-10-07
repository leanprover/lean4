// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.DSimp
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Elab.Tactic.Grind.DSimprocDSL import Lean.Meta.Sym.DSimp.Variant import Lean.Meta.Sym.DSimp.Reduce import Lean.Meta.Sym.DSimp.DSimproc import Lean.Meta.Sym.DSimp.Rewrite
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
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint64_t l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_ofNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_ofArray(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "invalid `dsimp` arguments, local declarations and `*` have been provided"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__4_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(lean_object* v___x_4_, lean_object* v_as_5_, size_t v_sz_6_, size_t v_i_7_, lean_object* v_b_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_a_13_; uint8_t v___x_17_; 
v___x_17_ = lean_usize_dec_lt(v_i_7_, v_sz_6_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v_b_8_);
return v___x_18_;
}
else
{
lean_object* v_snd_19_; lean_object* v_fst_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_69_; 
v_snd_19_ = lean_ctor_get(v_b_8_, 1);
v_fst_20_ = lean_ctor_get(v_b_8_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_b_8_);
if (v_isSharedCheck_69_ == 0)
{
v___x_22_ = v_b_8_;
v_isShared_23_ = v_isSharedCheck_69_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snd_19_);
lean_inc(v_fst_20_);
lean_dec(v_b_8_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_69_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_68_; 
v_fst_24_ = lean_ctor_get(v_snd_19_, 0);
v_snd_25_ = lean_ctor_get(v_snd_19_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_snd_19_);
if (v_isSharedCheck_68_ == 0)
{
v___x_27_ = v_snd_19_;
v_isShared_28_ = v_isSharedCheck_68_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_snd_25_);
lean_inc(v_fst_24_);
lean_dec(v_snd_19_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_68_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_a_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_a_29_ = lean_array_uget_borrowed(v_as_5_, v_i_7_);
lean_inc(v_a_29_);
v___x_30_ = l_Lean_Syntax_getKind(v_a_29_);
v___x_31_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___closed__1));
v___x_32_ = lean_name_eq(v___x_30_, v___x_31_);
lean_dec(v___x_30_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_35_; 
lean_dec(v_fst_24_);
v___x_33_ = lean_box(v___x_17_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_33_);
v___x_35_ = v___x_27_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_snd_25_);
v___x_35_ = v_reuseFailAlloc_39_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_35_);
v___x_37_ = v___x_22_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_fst_20_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
v_a_13_ = v___x_37_;
goto v___jp_12_;
}
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_Lean_Syntax_getId(v_a_29_);
v___x_41_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_4_, v___x_40_);
lean_dec(v___x_40_);
if (lean_obj_tag(v___x_41_) == 1)
{
lean_object* v_val_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v_val_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_val_42_);
lean_dec_ref_known(v___x_41_, 1);
v___x_43_ = l_Lean_LocalDecl_fvarId(v_val_42_);
lean_dec(v_val_42_);
v___x_44_ = lean_array_push(v_fst_20_, v___x_43_);
if (v_isShared_28_ == 0)
{
v___x_46_ = v___x_27_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_fst_24_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_snd_25_);
v___x_46_ = v_reuseFailAlloc_50_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_48_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_46_);
lean_ctor_set(v___x_22_, 0, v___x_44_);
v___x_48_ = v___x_22_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
v_a_13_ = v___x_48_;
goto v___jp_12_;
}
}
}
else
{
lean_object* v___x_51_; 
lean_dec(v___x_41_);
lean_inc(v_a_29_);
v___x_51_ = l_Lean_realizeGlobalConstNoOverload(v_a_29_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = lean_array_push(v_snd_25_, v_a_52_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 1, v___x_53_);
v___x_55_ = v___x_27_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_fst_24_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_59_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_57_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_55_);
v___x_57_ = v___x_22_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_fst_20_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
v_a_13_ = v___x_57_;
goto v___jp_12_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_del_object(v___x_27_);
lean_dec(v_snd_25_);
lean_dec(v_fst_24_);
lean_del_object(v___x_22_);
lean_dec(v_fst_20_);
v_a_60_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_51_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_51_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
}
}
}
v___jp_12_:
{
size_t v___x_14_; size_t v___x_15_; 
v___x_14_ = ((size_t)1ULL);
v___x_15_ = lean_usize_add(v_i_7_, v___x_14_);
v_i_7_ = v___x_15_;
v_b_8_ = v_a_13_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg___boxed(lean_object* v___x_70_, lean_object* v_as_71_, lean_object* v_sz_72_, lean_object* v_i_73_, lean_object* v_b_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
size_t v_sz_boxed_78_; size_t v_i_boxed_79_; lean_object* v_res_80_; 
v_sz_boxed_78_ = lean_unbox_usize(v_sz_72_);
lean_dec(v_sz_72_);
v_i_boxed_79_ = lean_unbox_usize(v_i_73_);
lean_dec(v_i_73_);
v_res_80_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_70_, v_as_71_, v_sz_boxed_78_, v_i_boxed_79_, v_b_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec_ref(v_as_71_);
lean_dec_ref(v___x_70_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1_spec__1(lean_object* v_msgData_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v_env_88_; uint8_t v___x_89_; lean_object* v_env_90_; lean_object* v___x_91_; lean_object* v_toCold_92_; lean_object* v_mctx_93_; lean_object* v_lctx_94_; lean_object* v_options_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_87_ = lean_st_ref_get(v___y_85_);
v_env_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_env_88_);
lean_dec(v___x_87_);
v___x_89_ = 0;
v_env_90_ = l_Lean_Environment_setRecordingDeps(v_env_88_, v___x_89_);
v___x_91_ = lean_st_ref_get(v___y_83_);
v_toCold_92_ = lean_ctor_get(v___y_84_, 0);
v_mctx_93_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_mctx_93_);
lean_dec(v___x_91_);
v_lctx_94_ = lean_ctor_get(v___y_82_, 2);
v_options_95_ = lean_ctor_get(v_toCold_92_, 2);
lean_inc_ref(v_options_95_);
lean_inc_ref(v_lctx_94_);
v___x_96_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_96_, 0, v_env_90_);
lean_ctor_set(v___x_96_, 1, v_mctx_93_);
lean_ctor_set(v___x_96_, 2, v_lctx_94_);
lean_ctor_set(v___x_96_, 3, v_options_95_);
v___x_97_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_msgData_81_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1_spec__1___boxed(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1_spec__1(v_msgData_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(lean_object* v_msg_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_ref_112_; lean_object* v___x_113_; lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_ref_112_ = lean_ctor_get(v___y_109_, 2);
v___x_113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1_spec__1(v_msg_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_inc(v_ref_112_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_ref_112_);
lean_ctor_set(v___x_118_, 1, v_a_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg___boxed(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_129_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3));
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
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2));
v_sz_159_ = lean_array_size(v_val_155_);
v___x_160_ = ((size_t)0ULL);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v_lctx_156_, v_val_155_, v_sz_159_, v___x_160_, v___x_158_, v_a_152_, v_a_153_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_189_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_189_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_189_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_189_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_snd_166_; lean_object* v_fst_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_snd_166_ = lean_ctor_get(v_a_162_, 1);
lean_inc(v_snd_166_);
v_fst_167_ = lean_ctor_get(v_a_162_, 0);
lean_inc(v_fst_167_);
lean_dec(v_a_162_);
v_fst_168_ = lean_ctor_get(v_snd_166_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v_snd_166_, 1);
lean_inc(v_snd_169_);
lean_dec(v_snd_166_);
v___x_176_ = lean_array_get_size(v_fst_167_);
v___x_177_ = lean_nat_dec_eq(v___x_176_, v___x_157_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; 
v___x_178_ = lean_unbox(v_fst_168_);
if (v___x_178_ == 0)
{
goto v___jp_170_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_snd_169_);
lean_dec(v_fst_168_);
lean_dec(v_fst_167_);
lean_del_object(v___x_164_);
v___x_179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4);
v___x_180_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(v___x_179_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
goto v___jp_170_;
}
v___jp_170_:
{
lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_174_; 
v___x_171_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_171_, 0, v_fst_167_);
lean_ctor_set(v___x_171_, 1, v_snd_169_);
v___x_172_ = lean_unbox(v_fst_168_);
lean_dec(v_fst_168_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*2, v___x_172_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_171_);
v___x_174_ = v___x_164_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_171_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_161_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_161_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__5));
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___boxed(lean_object* v_args_x3f_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v_args_x3f_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_args_x3f_200_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object* v___x_211_, lean_object* v_as_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___redArg(v___x_211_, v_as_212_, v_sz_213_, v_i_214_, v_b_215_, v___y_222_, v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object* v___x_226_, lean_object* v_as_227_, lean_object* v_sz_228_, lean_object* v_i_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
size_t v_sz_boxed_240_; size_t v_i_boxed_241_; lean_object* v_res_242_; 
v_sz_boxed_240_ = lean_unbox_usize(v_sz_228_);
lean_dec(v_sz_228_);
v_i_boxed_241_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(v___x_226_, v_as_227_, v_sz_boxed_240_, v_i_boxed_241_, v_b_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_as_227_);
lean_dec_ref(v___x_226_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(lean_object* v_00_u03b1_243_, lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(v_msg_244_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___boxed(lean_object* v_00_u03b1_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(v_00_u03b1_255_, v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0(lean_object* v_post_267_, lean_object* v_a_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc_ref(v___y_275_);
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
v___x_280_ = lean_apply_11(v_post_267_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, lean_box(0));
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
if (lean_obj_tag(v_a_281_) == 0)
{
uint8_t v_done_282_; 
v_done_282_ = lean_ctor_get_uint8(v_a_281_, 0);
lean_dec_ref_known(v_a_281_, 0);
if (v_done_282_ == 0)
{
lean_object* v___x_283_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_283_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_a_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
return v___x_283_;
}
else
{
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v___x_280_;
}
}
else
{
uint8_t v_done_284_; 
lean_dec_ref(v___y_269_);
v_done_284_ = lean_ctor_get_uint8(v_a_281_, sizeof(void*)*1);
if (v_done_284_ == 0)
{
lean_object* v_e_x27_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref_known(v___x_280_, 1);
v_e_x27_285_ = lean_ctor_get(v_a_281_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_a_281_);
if (v_isSharedCheck_303_ == 0)
{
v___x_287_ = v_a_281_;
v_isShared_288_ = v_isSharedCheck_303_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_e_x27_285_);
lean_dec(v_a_281_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_303_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; 
lean_inc_ref(v_e_x27_285_);
v___x_289_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_a_268_, v_e_x27_285_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
if (lean_obj_tag(v_a_290_) == 0)
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_301_; 
lean_inc_ref(v_a_290_);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_289_, 0);
lean_dec(v_unused_302_);
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
else
{
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v_done_294_; lean_object* v___x_296_; 
v_done_294_ = lean_ctor_get_uint8(v_a_290_, 0);
lean_dec_ref_known(v_a_290_, 0);
if (v_isShared_288_ == 0)
{
v___x_296_ = v___x_287_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_e_x27_285_);
v___x_296_ = v_reuseFailAlloc_300_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v_done_294_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_296_);
v___x_298_ = v___x_292_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_del_object(v___x_287_);
lean_dec_ref(v_e_x27_285_);
return v___x_289_;
}
}
else
{
lean_del_object(v___x_287_);
lean_dec_ref(v_e_x27_285_);
return v___x_289_;
}
}
}
else
{
lean_dec_ref_known(v_a_281_, 1);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
return v___x_280_;
}
}
}
else
{
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0___boxed(lean_object* v_post_304_, lean_object* v_a_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0(v_post_304_, v_a_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec_ref(v_a_305_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1(lean_object* v_fvarIds_318_, lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = l_Lean_FVarIdSet_ofArray(v_fvarIds_318_);
v___x_332_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v___x_331_, v___y_320_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1___boxed(lean_object* v_fvarIds_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1(v_fvarIds_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v_fvarIds_333_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2(lean_object* v_pre_347_, lean_object* v___f_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
lean_inc(v___y_350_);
lean_inc_ref(v___y_349_);
v___x_361_ = lean_apply_11(v_pre_347_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
if (lean_obj_tag(v_a_362_) == 0)
{
uint8_t v_done_363_; 
v_done_363_ = lean_ctor_get_uint8(v_a_362_, 0);
lean_dec_ref_known(v_a_362_, 0);
if (v_done_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref_known(v___x_361_, 1);
v___x_364_ = lean_apply_12(v___f_348_, v___x_360_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
return v___x_364_;
}
else
{
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v___f_348_);
return v___x_361_;
}
}
else
{
uint8_t v_done_365_; 
lean_dec_ref(v___y_349_);
v_done_365_ = lean_ctor_get_uint8(v_a_362_, sizeof(void*)*1);
if (v_done_365_ == 0)
{
lean_object* v_e_x27_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref_known(v___x_361_, 1);
v_e_x27_366_ = lean_ctor_get(v_a_362_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_384_ == 0)
{
v___x_368_ = v_a_362_;
v_isShared_369_ = v_isSharedCheck_384_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_e_x27_366_);
lean_dec(v_a_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_384_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; 
lean_inc_ref(v_e_x27_366_);
v___x_370_ = lean_apply_12(v___f_348_, v___x_360_, v_e_x27_366_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
if (lean_obj_tag(v_a_371_) == 0)
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_382_; 
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_383_);
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
else
{
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
uint8_t v_done_375_; lean_object* v___x_377_; 
v_done_375_ = lean_ctor_get_uint8(v_a_371_, 0);
lean_dec_ref_known(v_a_371_, 0);
if (v_isShared_369_ == 0)
{
v___x_377_ = v___x_368_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_e_x27_366_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v_done_375_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_377_);
v___x_379_ = v___x_373_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
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
else
{
lean_dec_ref_known(v_a_371_, 1);
lean_del_object(v___x_368_);
lean_dec_ref(v_e_x27_366_);
return v___x_370_;
}
}
else
{
lean_del_object(v___x_368_);
lean_dec_ref(v_e_x27_366_);
return v___x_370_;
}
}
}
else
{
lean_dec_ref_known(v_a_362_, 1);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___f_348_);
return v___x_361_;
}
}
}
else
{
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v___f_348_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2___boxed(lean_object* v_pre_385_, lean_object* v___f_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2(v_pre_385_, v___f_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3(lean_object* v_pre_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc_ref(v___y_400_);
v___x_411_ = lean_apply_11(v_pre_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, lean_box(0));
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
if (lean_obj_tag(v_a_412_) == 0)
{
uint8_t v_done_413_; 
v_done_413_ = lean_ctor_get_uint8(v_a_412_, 0);
lean_dec_ref_known(v_a_412_, 0);
if (v_done_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec_ref_known(v___x_411_, 1);
v___x_414_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_400_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v___x_414_;
}
else
{
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec_ref(v___y_400_);
return v___x_411_;
}
}
else
{
uint8_t v_done_415_; 
lean_dec_ref(v___y_400_);
v_done_415_ = lean_ctor_get_uint8(v_a_412_, sizeof(void*)*1);
if (v_done_415_ == 0)
{
lean_object* v_e_x27_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref_known(v___x_411_, 1);
v_e_x27_416_ = lean_ctor_get(v_a_412_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_412_);
if (v_isSharedCheck_434_ == 0)
{
v___x_418_ = v_a_412_;
v_isShared_419_ = v_isSharedCheck_434_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_e_x27_416_);
lean_dec(v_a_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_434_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; 
lean_inc_ref(v_e_x27_416_);
v___x_420_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_416_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
if (lean_obj_tag(v_a_421_) == 0)
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
lean_inc_ref(v_a_421_);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_420_, 0);
lean_dec(v_unused_433_);
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint8_t v_done_425_; lean_object* v___x_427_; 
v_done_425_ = lean_ctor_get_uint8(v_a_421_, 0);
lean_dec_ref_known(v_a_421_, 0);
if (v_isShared_419_ == 0)
{
v___x_427_ = v___x_418_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_e_x27_416_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*1, v_done_425_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_del_object(v___x_418_);
lean_dec_ref(v_e_x27_416_);
return v___x_420_;
}
}
else
{
lean_del_object(v___x_418_);
lean_dec_ref(v_e_x27_416_);
return v___x_420_;
}
}
}
else
{
lean_dec_ref_known(v_a_412_, 1);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v___x_411_;
}
}
}
else
{
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec_ref(v___y_400_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3___boxed(lean_object* v_pre_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3(v_pre_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(lean_object* v_methods_448_, lean_object* v_args_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___y_456_; lean_object* v_post_457_; lean_object* v_pre_460_; lean_object* v_post_461_; lean_object* v_fvarIds_462_; uint8_t v_zetaDeltaAll_463_; lean_object* v_declNames_464_; lean_object* v_pre_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v_pre_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; 
v_pre_460_ = lean_ctor_get(v_methods_448_, 0);
lean_inc_ref(v_pre_460_);
v_post_461_ = lean_ctor_get(v_methods_448_, 1);
lean_inc_ref(v_post_461_);
lean_dec_ref(v_methods_448_);
v_fvarIds_462_ = lean_ctor_get(v_args_449_, 0);
lean_inc_ref(v_fvarIds_462_);
v_zetaDeltaAll_463_ = lean_ctor_get_uint8(v_args_449_, sizeof(void*)*2);
v_declNames_464_ = lean_ctor_get(v_args_449_, 1);
lean_inc_ref(v_declNames_464_);
lean_dec_ref(v_args_449_);
if (v_zetaDeltaAll_463_ == 0)
{
v_pre_486_ = v_pre_460_;
v___y_487_ = v_a_450_;
v___y_488_ = v_a_451_;
v___y_489_ = v_a_452_;
v___y_490_ = v_a_453_;
goto v___jp_485_;
}
else
{
lean_object* v_pre_496_; 
v_pre_496_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_496_, 0, v_pre_460_);
v_pre_486_ = v_pre_496_;
v___y_487_ = v_a_450_;
v___y_488_ = v_a_451_;
v___y_489_ = v_a_452_;
v___y_490_ = v_a_453_;
goto v___jp_485_;
}
v___jp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___y_456_);
lean_ctor_set(v___x_458_, 1, v_post_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
v___jp_465_:
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_array_get_size(v_declNames_464_);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_Sym_DSimp_Decls_ofNames(v_declNames_464_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec_ref(v_declNames_464_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___f_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___f_476_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_476_, 0, v_post_461_);
lean_closure_set(v___f_476_, 1, v_a_475_);
v___y_456_ = v_pre_466_;
v_post_457_ = v___f_476_;
goto v___jp_455_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_pre_466_);
lean_dec_ref(v_post_461_);
v_a_477_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_474_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_474_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_dec_ref(v_declNames_464_);
v___y_456_ = v_pre_466_;
v_post_457_ = v_post_461_;
goto v___jp_455_;
}
}
v___jp_485_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_array_get_size(v_fvarIds_462_);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_nat_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___f_494_; lean_object* v_pre_495_; 
v___f_494_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_494_, 0, v_fvarIds_462_);
v_pre_495_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2___boxed), 13, 2);
lean_closure_set(v_pre_495_, 0, v_pre_486_);
lean_closure_set(v_pre_495_, 1, v___f_494_);
v_pre_466_ = v_pre_495_;
v___y_467_ = v___y_487_;
v___y_468_ = v___y_488_;
v___y_469_ = v___y_489_;
v___y_470_ = v___y_490_;
goto v___jp_465_;
}
else
{
lean_dec_ref(v_fvarIds_462_);
v_pre_466_ = v_pre_486_;
v___y_467_ = v___y_487_;
v___y_468_ = v___y_488_;
v___y_469_ = v___y_489_;
v___y_470_ = v___y_490_;
goto v___jp_465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___boxed(lean_object* v_methods_497_, lean_object* v_args_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v_methods_497_, v_args_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(lean_object* v_methods_505_, lean_object* v_args_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v_methods_505_, v_args_506_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed(lean_object* v_methods_517_, lean_object* v_args_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(v_methods_517_, v_args_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
lean_inc_ref(v___y_530_);
v___x_541_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_530_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
if (lean_obj_tag(v_a_542_) == 0)
{
uint8_t v_done_543_; 
v_done_543_ = lean_ctor_get_uint8(v_a_542_, 0);
lean_dec_ref_known(v_a_542_, 0);
if (v_done_543_ == 0)
{
lean_object* v___x_544_; 
lean_dec_ref_known(v___x_541_, 1);
v___x_544_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_530_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec_ref(v___y_530_);
return v___x_544_;
}
else
{
lean_dec_ref(v___y_530_);
return v___x_541_;
}
}
else
{
uint8_t v_done_545_; 
lean_dec_ref(v___y_530_);
v_done_545_ = lean_ctor_get_uint8(v_a_542_, sizeof(void*)*1);
if (v_done_545_ == 0)
{
lean_object* v_e_x27_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref_known(v___x_541_, 1);
v_e_x27_546_ = lean_ctor_get(v_a_542_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_542_);
if (v_isSharedCheck_564_ == 0)
{
v___x_548_ = v_a_542_;
v_isShared_549_ = v_isSharedCheck_564_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_e_x27_546_);
lean_dec(v_a_542_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_564_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_546_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
if (lean_obj_tag(v_a_551_) == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_562_; 
lean_inc_ref(v_a_551_);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_550_, 0);
lean_dec(v_unused_563_);
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
else
{
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint8_t v_done_555_; lean_object* v___x_557_; 
v_done_555_ = lean_ctor_get_uint8(v_a_551_, 0);
lean_dec_ref_known(v_a_551_, 0);
if (v_isShared_549_ == 0)
{
v___x_557_ = v___x_548_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_e_x27_546_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*1, v_done_555_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_557_);
v___x_559_ = v___x_553_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
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
lean_del_object(v___x_548_);
lean_dec_ref(v_e_x27_546_);
return v___x_550_;
}
}
else
{
lean_del_object(v___x_548_);
lean_dec_ref(v_e_x27_546_);
return v___x_550_;
}
}
}
else
{
lean_dec_ref_known(v_a_542_, 1);
return v___x_541_;
}
}
}
else
{
lean_dec_ref(v___y_530_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0___boxed(lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(lean_object* v___f_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
lean_inc_ref(v___y_579_);
v___x_591_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_579_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
if (lean_obj_tag(v_a_592_) == 0)
{
uint8_t v_done_593_; 
v_done_593_ = lean_ctor_get_uint8(v_a_592_, 0);
lean_dec_ref_known(v_a_592_, 0);
if (v_done_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec_ref_known(v___x_591_, 1);
v___x_594_ = lean_apply_12(v___f_578_, v___x_590_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
return v___x_594_;
}
else
{
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v___f_578_);
return v___x_591_;
}
}
else
{
uint8_t v_done_595_; 
lean_dec_ref(v___y_579_);
v_done_595_ = lean_ctor_get_uint8(v_a_592_, sizeof(void*)*1);
if (v_done_595_ == 0)
{
lean_object* v_e_x27_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref_known(v___x_591_, 1);
v_e_x27_596_ = lean_ctor_get(v_a_592_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_a_592_);
if (v_isSharedCheck_614_ == 0)
{
v___x_598_ = v_a_592_;
v_isShared_599_ = v_isSharedCheck_614_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_e_x27_596_);
lean_dec(v_a_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_614_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; 
lean_inc_ref(v_e_x27_596_);
v___x_600_ = lean_apply_12(v___f_578_, v___x_590_, v_e_x27_596_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
if (lean_obj_tag(v_a_601_) == 0)
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_612_; 
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_613_);
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_612_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_612_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
uint8_t v_done_605_; lean_object* v___x_607_; 
v_done_605_ = lean_ctor_get_uint8(v_a_601_, 0);
lean_dec_ref_known(v_a_601_, 0);
if (v_isShared_599_ == 0)
{
v___x_607_ = v___x_598_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_e_x27_596_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*1, v_done_605_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_607_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_601_, 1);
lean_del_object(v___x_598_);
lean_dec_ref(v_e_x27_596_);
return v___x_600_;
}
}
else
{
lean_del_object(v___x_598_);
lean_dec_ref(v_e_x27_596_);
return v___x_600_;
}
}
}
else
{
lean_dec_ref_known(v_a_592_, 1);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___f_578_);
return v___x_591_;
}
}
}
else
{
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v___f_578_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1___boxed(lean_object* v___f_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(v___f_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(lean_object* v_args_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3));
v___x_643_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v___x_642_, v_args_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___boxed(lean_object* v_args_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(lean_object* v_args_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_651_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___boxed(lean_object* v_args_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(v_args_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg(){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0));
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___boxed(lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(lean_object* v_x_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed(lean_object* v_x_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(v_x_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_x_692_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(lean_object* v_stx_x3f_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
if (lean_obj_tag(v_stx_x3f_704_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; 
v_val_714_ = lean_ctor_get(v_stx_x3f_704_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_stx_x3f_704_, 1);
v___x_715_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(v_val_714_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_stx_x3f_704_);
v___x_716_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed), 11, 0);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc___boxed(lean_object* v_stx_x3f_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_stx_x3f_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_728_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0));
v___x_731_ = l_Lean_stringToMessageData(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(lean_object* v_variantName_738_, lean_object* v_args_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = l_Lean_Name_isAnonymous(v_variantName_738_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v_env_751_; lean_object* v___x_752_; 
v___x_750_ = lean_st_ref_get(v_a_747_);
v_env_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc_ref(v_env_751_);
lean_dec(v___x_750_);
v___x_752_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_751_, v_variantName_738_);
if (lean_obj_tag(v___x_752_) == 1)
{
lean_object* v_val_753_; lean_object* v_pre_x3f_754_; lean_object* v_post_x3f_755_; lean_object* v_config_756_; lean_object* v___x_757_; 
lean_dec(v_variantName_738_);
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v___x_752_, 1);
v_pre_x3f_754_ = lean_ctor_get(v_val_753_, 0);
lean_inc(v_pre_x3f_754_);
v_post_x3f_755_ = lean_ctor_get(v_val_753_, 1);
lean_inc(v_post_x3f_755_);
v_config_756_ = lean_ctor_get(v_val_753_, 2);
lean_inc_ref(v_config_756_);
lean_dec(v_val_753_);
v___x_757_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_pre_x3f_754_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_post_x3f_755_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_a_758_);
lean_ctor_set(v___x_761_, 1, v_a_760_);
v___x_762_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v___x_761_, v_args_739_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_a_763_);
lean_ctor_set(v___x_767_, 1, v_config_756_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_config_756_);
v_a_772_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_762_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_758_);
lean_dec_ref(v_config_756_);
lean_dec_ref(v_args_739_);
v_a_780_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_759_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_759_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_config_756_);
lean_dec(v_post_x3f_755_);
lean_dec_ref(v_args_739_);
v_a_788_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_757_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_757_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v___x_752_);
lean_dec_ref(v_args_739_);
v___x_796_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1);
v___x_797_ = l_Lean_MessageData_ofName(v_variantName_738_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(v___x_800_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_801_;
}
}
else
{
lean_object* v___x_802_; 
lean_dec(v_variantName_738_);
v___x_802_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_739_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_812_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__4));
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_803_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_802_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_802_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___boxed(lean_object* v_variantName_821_, lean_object* v_args_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v_variantName_821_, v_args_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_832_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_box(0);
v___x_834_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg(){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___boxed(lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(lean_object* v_00_u03b1_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___boxed(lean_object* v_00_u03b1_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(v_00_u03b1_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
lean_inc(v___y_868_);
lean_inc_ref(v___y_867_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
v___x_874_ = lean_apply_10(v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, lean_box(0));
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed(lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(v_x_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(lean_object* v_mvarId_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___f_899_; lean_object* v___x_900_; 
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_899_, 0, v_x_888_);
lean_closure_set(v___f_899_, 1, v___y_889_);
lean_closure_set(v___f_899_, 2, v___y_890_);
lean_closure_set(v___f_899_, 3, v___y_891_);
lean_closure_set(v___f_899_, 4, v___y_892_);
lean_closure_set(v___f_899_, 5, v___y_893_);
v___x_900_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_887_, v___f_899_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_900_) == 0)
{
return v___x_900_;
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
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
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___boxed(lean_object* v_mvarId_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_909_, v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(lean_object* v_00_u03b1_922_, lean_object* v_mvarId_923_, lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_923_, v_x_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed(lean_object* v_00_u03b1_936_, lean_object* v_mvarId_937_, lean_object* v_x_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(v_00_u03b1_936_, v_mvarId_937_, v_x_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(lean_object* v_mvarId_950_, lean_object* v_fst_951_, lean_object* v_snd_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_MVarId_getType(v_mvarId_950_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_966_, 0, v_a_965_);
v___x_967_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_966_, v_fst_951_, v_snd_952_, v___y_953_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
return v___x_967_;
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v___y_953_);
lean_dec_ref(v_snd_952_);
lean_dec_ref(v_fst_951_);
v_a_968_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_964_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed(lean_object* v_mvarId_976_, lean_object* v_fst_977_, lean_object* v_snd_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(v_mvarId_976_, v_fst_977_, v_snd_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
lean_object* v_ks_995_; lean_object* v_vs_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1020_; 
v_ks_995_ = lean_ctor_get(v_x_991_, 0);
v_vs_996_ = lean_ctor_get(v_x_991_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_x_991_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_998_ = v_x_991_;
v_isShared_999_ = v_isSharedCheck_1020_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_vs_996_);
lean_inc(v_ks_995_);
lean_dec(v_x_991_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1020_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_array_get_size(v_ks_995_);
v___x_1001_ = lean_nat_dec_lt(v_x_992_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_x_992_);
v___x_1002_ = lean_array_push(v_ks_995_, v_x_993_);
v___x_1003_ = lean_array_push(v_vs_996_, v_x_994_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1003_);
lean_ctor_set(v___x_998_, 0, v___x_1002_);
v___x_1005_ = v___x_998_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v_k_x27_1007_; uint8_t v___x_1008_; 
v_k_x27_1007_ = lean_array_fget_borrowed(v_ks_995_, v_x_992_);
v___x_1008_ = l_Lean_instBEqMVarId_beq(v_x_993_, v_k_x27_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1010_; 
if (v_isShared_999_ == 0)
{
v___x_1010_ = v___x_998_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_ks_995_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_vs_996_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_add(v_x_992_, v___x_1011_);
lean_dec(v_x_992_);
v_x_991_ = v___x_1010_;
v_x_992_ = v___x_1012_;
goto _start;
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1015_ = lean_array_fset(v_ks_995_, v_x_992_, v_x_993_);
v___x_1016_ = lean_array_fset(v_vs_996_, v_x_992_, v_x_994_);
lean_dec(v_x_992_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1016_);
lean_ctor_set(v___x_998_, 0, v___x_1015_);
v___x_1018_ = v___x_998_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1016_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(lean_object* v_n_1021_, lean_object* v_k_1022_, lean_object* v_v_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_n_1021_, v___x_1024_, v_k_1022_, v_v_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1027_, size_t v_x_1028_, size_t v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v_es_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v_j_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_es_1032_ = lean_ctor_get(v_x_1027_, 0);
v___x_1033_ = ((size_t)31ULL);
v___x_1034_ = lean_usize_land(v_x_1028_, v___x_1033_);
v_j_1035_ = lean_usize_to_nat(v___x_1034_);
v___x_1036_ = lean_array_get_size(v_es_1032_);
v___x_1037_ = lean_nat_dec_lt(v_j_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec(v_j_1035_);
lean_dec(v_x_1031_);
lean_dec(v_x_1030_);
return v_x_1027_;
}
else
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1076_; 
lean_inc_ref(v_es_1032_);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_x_1027_, 0);
lean_dec(v_unused_1077_);
v___x_1039_ = v_x_1027_;
v_isShared_1040_ = v_isSharedCheck_1076_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v_x_1027_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1076_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_v_1041_; lean_object* v___x_1042_; lean_object* v_xs_x27_1043_; lean_object* v___y_1045_; 
v_v_1041_ = lean_array_fget(v_es_1032_, v_j_1035_);
v___x_1042_ = lean_box(0);
v_xs_x27_1043_ = lean_array_fset(v_es_1032_, v_j_1035_, v___x_1042_);
switch(lean_obj_tag(v_v_1041_))
{
case 0:
{
lean_object* v_key_1050_; lean_object* v_val_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_key_1050_ = lean_ctor_get(v_v_1041_, 0);
v_val_1051_ = lean_ctor_get(v_v_1041_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_v_1041_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v_v_1041_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_val_1051_);
lean_inc(v_key_1050_);
lean_dec(v_v_1041_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Lean_instBEqMVarId_beq(v_x_1030_, v_key_1050_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_del_object(v___x_1053_);
v___x_1056_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1050_, v_val_1051_, v_x_1030_, v_x_1031_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
v___y_1045_ = v___x_1057_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_val_1051_);
lean_dec(v_key_1050_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v_x_1031_);
lean_ctor_set(v___x_1053_, 0, v_x_1030_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_x_1030_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_x_1031_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
v___y_1045_ = v___x_1059_;
goto v___jp_1044_;
}
}
}
}
case 1:
{
lean_object* v_node_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1074_; 
v_node_1062_ = lean_ctor_get(v_v_1041_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_v_1041_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1064_ = v_v_1041_;
v_isShared_1065_ = v_isSharedCheck_1074_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_node_1062_);
lean_dec(v_v_1041_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1074_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1066_ = ((size_t)5ULL);
v___x_1067_ = lean_usize_shift_right(v_x_1028_, v___x_1066_);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_x_1029_, v___x_1068_);
v___x_1070_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_node_1062_, v___x_1067_, v___x_1069_, v_x_1030_, v_x_1031_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1070_);
v___x_1072_ = v___x_1064_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v___y_1045_ = v___x_1072_;
goto v___jp_1044_;
}
}
}
default: 
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_x_1030_);
lean_ctor_set(v___x_1075_, 1, v_x_1031_);
v___y_1045_ = v___x_1075_;
goto v___jp_1044_;
}
}
v___jp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_array_fset(v_xs_x27_1043_, v_j_1035_, v___y_1045_);
lean_dec(v_j_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1046_);
v___x_1048_ = v___x_1039_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
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
}
else
{
lean_object* v_ks_1078_; lean_object* v_vs_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1097_; 
v_ks_1078_ = lean_ctor_get(v_x_1027_, 0);
v_vs_1079_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1081_ = v_x_1027_;
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_vs_1079_);
lean_inc(v_ks_1078_);
lean_dec(v_x_1027_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1097_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_ks_1078_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_vs_1079_);
v___x_1084_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v_newNode_1085_; size_t v___x_1086_; uint8_t v___x_1087_; 
v_newNode_1085_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v___x_1084_, v_x_1030_, v_x_1031_);
v___x_1086_ = ((size_t)7ULL);
v___x_1087_ = lean_usize_dec_le(v___x_1086_, v_x_1029_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1085_);
v___x_1089_ = lean_unsigned_to_nat(4u);
v___x_1090_ = lean_nat_dec_lt(v___x_1088_, v___x_1089_);
lean_dec(v___x_1088_);
if (v___x_1090_ == 0)
{
lean_object* v_ks_1091_; lean_object* v_vs_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_ks_1091_ = lean_ctor_get(v_newNode_1085_, 0);
lean_inc_ref(v_ks_1091_);
v_vs_1092_ = lean_ctor_get(v_newNode_1085_, 1);
lean_inc_ref(v_vs_1092_);
lean_dec_ref(v_newNode_1085_);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0);
v___x_1095_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_x_1029_, v_ks_1091_, v_vs_1092_, v___x_1093_, v___x_1094_);
lean_dec_ref(v_vs_1092_);
lean_dec_ref(v_ks_1091_);
return v___x_1095_;
}
else
{
return v_newNode_1085_;
}
}
else
{
return v_newNode_1085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(size_t v_depth_1098_, lean_object* v_keys_1099_, lean_object* v_vals_1100_, lean_object* v_i_1101_, lean_object* v_entries_1102_){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_array_get_size(v_keys_1099_);
v___x_1104_ = lean_nat_dec_lt(v_i_1101_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec(v_i_1101_);
return v_entries_1102_;
}
else
{
lean_object* v_k_1105_; lean_object* v_v_1106_; uint64_t v___x_1107_; size_t v_h_1108_; size_t v___x_1109_; lean_object* v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v_h_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_k_1105_ = lean_array_fget_borrowed(v_keys_1099_, v_i_1101_);
v_v_1106_ = lean_array_fget_borrowed(v_vals_1100_, v_i_1101_);
v___x_1107_ = l_Lean_instHashableMVarId_hash(v_k_1105_);
v_h_1108_ = lean_uint64_to_usize(v___x_1107_);
v___x_1109_ = ((size_t)5ULL);
v___x_1110_ = lean_unsigned_to_nat(1u);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = lean_usize_sub(v_depth_1098_, v___x_1111_);
v___x_1113_ = lean_usize_mul(v___x_1109_, v___x_1112_);
v_h_1114_ = lean_usize_shift_right(v_h_1108_, v___x_1113_);
v___x_1115_ = lean_nat_add(v_i_1101_, v___x_1110_);
lean_dec(v_i_1101_);
lean_inc(v_v_1106_);
lean_inc(v_k_1105_);
v___x_1116_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_entries_1102_, v_h_1114_, v_depth_1098_, v_k_1105_, v_v_1106_);
v_i_1101_ = v___x_1115_;
v_entries_1102_ = v___x_1116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_1118_, lean_object* v_keys_1119_, lean_object* v_vals_1120_, lean_object* v_i_1121_, lean_object* v_entries_1122_){
_start:
{
size_t v_depth_boxed_1123_; lean_object* v_res_1124_; 
v_depth_boxed_1123_ = lean_unbox_usize(v_depth_1118_);
lean_dec(v_depth_1118_);
v_res_1124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_boxed_1123_, v_keys_1119_, v_vals_1120_, v_i_1121_, v_entries_1122_);
lean_dec_ref(v_vals_1120_);
lean_dec_ref(v_keys_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
size_t v_x_8773__boxed_1130_; size_t v_x_8774__boxed_1131_; lean_object* v_res_1132_; 
v_x_8773__boxed_1130_ = lean_unbox_usize(v_x_1126_);
lean_dec(v_x_1126_);
v_x_8774__boxed_1131_ = lean_unbox_usize(v_x_1127_);
lean_dec(v_x_1127_);
v_res_1132_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1125_, v_x_8773__boxed_1130_, v_x_8774__boxed_1131_, v_x_1128_, v_x_1129_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
uint64_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = l_Lean_instHashableMVarId_hash(v_x_1134_);
v___x_1137_ = lean_uint64_to_usize(v___x_1136_);
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1133_, v___x_1137_, v___x_1138_, v_x_1134_, v_x_1135_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object* v_mvarId_1140_, lean_object* v_val_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_mctx_1145_; lean_object* v_cache_1146_; lean_object* v_zetaDeltaFVarIds_1147_; lean_object* v_postponed_1148_; lean_object* v_diag_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1179_; 
v___x_1144_ = lean_st_ref_take(v___y_1142_);
v_mctx_1145_ = lean_ctor_get(v___x_1144_, 0);
v_cache_1146_ = lean_ctor_get(v___x_1144_, 1);
v_zetaDeltaFVarIds_1147_ = lean_ctor_get(v___x_1144_, 2);
v_postponed_1148_ = lean_ctor_get(v___x_1144_, 3);
v_diag_1149_ = lean_ctor_get(v___x_1144_, 4);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1151_ = v___x_1144_;
v_isShared_1152_ = v_isSharedCheck_1179_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_diag_1149_);
lean_inc(v_postponed_1148_);
lean_inc(v_zetaDeltaFVarIds_1147_);
lean_inc(v_cache_1146_);
lean_inc(v_mctx_1145_);
lean_dec(v___x_1144_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1179_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_depth_1153_; lean_object* v_levelAssignDepth_1154_; lean_object* v_lmvarCounter_1155_; lean_object* v_mvarCounter_1156_; lean_object* v_lDecls_1157_; lean_object* v_decls_1158_; lean_object* v_userNames_1159_; lean_object* v_lAssignment_1160_; lean_object* v_eAssignment_1161_; lean_object* v_dAssignment_1162_; lean_object* v_instanceTypedMVars_1163_; lean_object* v_synthNormMemo_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1178_; 
v_depth_1153_ = lean_ctor_get(v_mctx_1145_, 0);
v_levelAssignDepth_1154_ = lean_ctor_get(v_mctx_1145_, 1);
v_lmvarCounter_1155_ = lean_ctor_get(v_mctx_1145_, 2);
v_mvarCounter_1156_ = lean_ctor_get(v_mctx_1145_, 3);
v_lDecls_1157_ = lean_ctor_get(v_mctx_1145_, 4);
v_decls_1158_ = lean_ctor_get(v_mctx_1145_, 5);
v_userNames_1159_ = lean_ctor_get(v_mctx_1145_, 6);
v_lAssignment_1160_ = lean_ctor_get(v_mctx_1145_, 7);
v_eAssignment_1161_ = lean_ctor_get(v_mctx_1145_, 8);
v_dAssignment_1162_ = lean_ctor_get(v_mctx_1145_, 9);
v_instanceTypedMVars_1163_ = lean_ctor_get(v_mctx_1145_, 10);
v_synthNormMemo_1164_ = lean_ctor_get(v_mctx_1145_, 11);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_mctx_1145_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1166_ = v_mctx_1145_;
v_isShared_1167_ = v_isSharedCheck_1178_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_synthNormMemo_1164_);
lean_inc(v_instanceTypedMVars_1163_);
lean_inc(v_dAssignment_1162_);
lean_inc(v_eAssignment_1161_);
lean_inc(v_lAssignment_1160_);
lean_inc(v_userNames_1159_);
lean_inc(v_decls_1158_);
lean_inc(v_lDecls_1157_);
lean_inc(v_mvarCounter_1156_);
lean_inc(v_lmvarCounter_1155_);
lean_inc(v_levelAssignDepth_1154_);
lean_inc(v_depth_1153_);
lean_dec(v_mctx_1145_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1178_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1168_ = lean_box(0);
v___x_1169_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_eAssignment_1161_, v_mvarId_1140_, v_val_1141_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 8, v___x_1169_);
v___x_1171_ = v___x_1166_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_depth_1153_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_levelAssignDepth_1154_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_lmvarCounter_1155_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_mvarCounter_1156_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_lDecls_1157_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_decls_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_userNames_1159_);
lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_lAssignment_1160_);
lean_ctor_set(v_reuseFailAlloc_1177_, 8, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1177_, 9, v_dAssignment_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 10, v_instanceTypedMVars_1163_);
lean_ctor_set(v_reuseFailAlloc_1177_, 11, v_synthNormMemo_1164_);
v___x_1171_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1171_);
v___x_1173_ = v___x_1151_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_cache_1146_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_zetaDeltaFVarIds_1147_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_postponed_1148_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_diag_1149_);
v___x_1173_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_st_ref_put(v___y_1142_, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1168_);
return v___x_1175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object* v_mvarId_1180_, lean_object* v_val_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1180_, v_val_1181_, v___y_1182_);
lean_dec(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object* v_a_1185_, lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = 0;
return v___x_1187_;
}
else
{
lean_object* v_key_1188_; lean_object* v_tail_1189_; uint8_t v___x_1190_; 
v_key_1188_ = lean_ctor_get(v_x_1186_, 0);
v_tail_1189_ = lean_ctor_get(v_x_1186_, 2);
v___x_1190_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1188_, v_a_1185_);
if (v___x_1190_ == 0)
{
v_x_1186_ = v_tail_1189_;
goto _start;
}
else
{
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg___boxed(lean_object* v_a_1192_, lean_object* v_x_1193_){
_start:
{
uint8_t v_res_1194_; lean_object* v_r_1195_; 
v_res_1194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1192_, v_x_1193_);
lean_dec(v_x_1193_);
lean_dec_ref(v_a_1192_);
v_r_1195_ = lean_box(v_res_1194_);
return v_r_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(lean_object* v_a_1196_, lean_object* v_b_1197_, lean_object* v_x_1198_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 0)
{
lean_dec(v_b_1197_);
lean_dec_ref(v_a_1196_);
return v_x_1198_;
}
else
{
lean_object* v_key_1199_; lean_object* v_value_1200_; lean_object* v_tail_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1213_; 
v_key_1199_ = lean_ctor_get(v_x_1198_, 0);
v_value_1200_ = lean_ctor_get(v_x_1198_, 1);
v_tail_1201_ = lean_ctor_get(v_x_1198_, 2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_x_1198_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1203_ = v_x_1198_;
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_tail_1201_);
lean_inc(v_value_1200_);
lean_inc(v_key_1199_);
lean_dec(v_x_1198_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1199_, v_a_1196_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1196_, v_b_1197_, v_tail_1201_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 2, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_key_1199_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_value_1200_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
lean_object* v___x_1211_; 
lean_dec(v_value_1200_);
lean_dec(v_key_1199_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_b_1197_);
lean_ctor_set(v___x_1203_, 0, v_a_1196_);
v___x_1211_ = v___x_1203_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1196_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_b_1197_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_tail_1201_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1214_, lean_object* v_x_1215_){
_start:
{
if (lean_obj_tag(v_x_1215_) == 0)
{
return v_x_1214_;
}
else
{
lean_object* v_key_1216_; lean_object* v_value_1217_; lean_object* v_tail_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1241_; 
v_key_1216_ = lean_ctor_get(v_x_1215_, 0);
v_value_1217_ = lean_ctor_get(v_x_1215_, 1);
v_tail_1218_ = lean_ctor_get(v_x_1215_, 2);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_x_1215_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1220_ = v_x_1215_;
v_isShared_1221_ = v_isSharedCheck_1241_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_tail_1218_);
lean_inc(v_value_1217_);
lean_inc(v_key_1216_);
lean_dec(v_x_1215_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1241_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v_fold_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1222_ = lean_array_get_size(v_x_1214_);
v___x_1223_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_key_1216_);
v___x_1224_ = 32ULL;
v___x_1225_ = lean_uint64_shift_right(v___x_1223_, v___x_1224_);
v_fold_1226_ = lean_uint64_xor(v___x_1223_, v___x_1225_);
v___x_1227_ = 16ULL;
v___x_1228_ = lean_uint64_shift_right(v_fold_1226_, v___x_1227_);
v___x_1229_ = lean_uint64_xor(v_fold_1226_, v___x_1228_);
v___x_1230_ = lean_uint64_to_usize(v___x_1229_);
v___x_1231_ = lean_usize_of_nat(v___x_1222_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_sub(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_usize_land(v___x_1230_, v___x_1233_);
v___x_1235_ = lean_array_uget_borrowed(v_x_1214_, v___x_1234_);
lean_inc(v___x_1235_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 2, v___x_1235_);
v___x_1237_ = v___x_1220_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_key_1216_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_value_1217_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_array_uset(v_x_1214_, v___x_1234_, v___x_1237_);
v_x_1214_ = v___x_1238_;
v_x_1215_ = v_tail_1218_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1242_, lean_object* v_source_1243_, lean_object* v_target_1244_){
_start:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_array_get_size(v_source_1243_);
v___x_1246_ = lean_nat_dec_lt(v_i_1242_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v_source_1243_);
lean_dec(v_i_1242_);
return v_target_1244_;
}
else
{
lean_object* v_es_1247_; lean_object* v___x_1248_; lean_object* v_source_1249_; lean_object* v_target_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_es_1247_ = lean_array_fget(v_source_1243_, v_i_1242_);
v___x_1248_ = lean_box(0);
v_source_1249_ = lean_array_fset(v_source_1243_, v_i_1242_, v___x_1248_);
v_target_1250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1244_, v_es_1247_);
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_add(v_i_1242_, v___x_1251_);
lean_dec(v_i_1242_);
v_i_1242_ = v___x_1252_;
v_source_1243_ = v_source_1249_;
v_target_1244_ = v_target_1250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(lean_object* v_data_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_nbuckets_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1255_ = lean_array_get_size(v_data_1254_);
v___x_1256_ = lean_unsigned_to_nat(2u);
v_nbuckets_1257_ = lean_nat_mul(v___x_1255_, v___x_1256_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_mk_array(v_nbuckets_1257_, v___x_1259_);
v___x_1261_ = lean_array_propagate_mark(v_data_1254_, v___x_1260_);
v___x_1262_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v___x_1258_, v_data_1254_, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object* v_m_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_){
_start:
{
lean_object* v_size_1266_; lean_object* v_buckets_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1310_; 
v_size_1266_ = lean_ctor_get(v_m_1263_, 0);
v_buckets_1267_ = lean_ctor_get(v_m_1263_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_m_1263_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1269_ = v_m_1263_;
v_isShared_1270_ = v_isSharedCheck_1310_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_buckets_1267_);
lean_inc(v_size_1266_);
lean_dec(v_m_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1310_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v_fold_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v_bkt_1284_; uint8_t v___x_1285_; 
v___x_1271_ = lean_array_get_size(v_buckets_1267_);
v___x_1272_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1264_);
v___x_1273_ = 32ULL;
v___x_1274_ = lean_uint64_shift_right(v___x_1272_, v___x_1273_);
v_fold_1275_ = lean_uint64_xor(v___x_1272_, v___x_1274_);
v___x_1276_ = 16ULL;
v___x_1277_ = lean_uint64_shift_right(v_fold_1275_, v___x_1276_);
v___x_1278_ = lean_uint64_xor(v_fold_1275_, v___x_1277_);
v___x_1279_ = lean_uint64_to_usize(v___x_1278_);
v___x_1280_ = lean_usize_of_nat(v___x_1271_);
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_sub(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_usize_land(v___x_1279_, v___x_1282_);
v_bkt_1284_ = lean_array_uget_borrowed(v_buckets_1267_, v___x_1283_);
v___x_1285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1264_, v_bkt_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v_size_x27_1287_; lean_object* v___x_1288_; lean_object* v_buckets_x27_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1286_ = lean_unsigned_to_nat(1u);
v_size_x27_1287_ = lean_nat_add(v_size_1266_, v___x_1286_);
lean_dec(v_size_1266_);
lean_inc(v_bkt_1284_);
v___x_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1288_, 0, v_a_1264_);
lean_ctor_set(v___x_1288_, 1, v_b_1265_);
lean_ctor_set(v___x_1288_, 2, v_bkt_1284_);
v_buckets_x27_1289_ = lean_array_uset(v_buckets_1267_, v___x_1283_, v___x_1288_);
v___x_1290_ = lean_unsigned_to_nat(4u);
v___x_1291_ = lean_nat_mul(v_size_x27_1287_, v___x_1290_);
v___x_1292_ = lean_unsigned_to_nat(3u);
v___x_1293_ = lean_nat_div(v___x_1291_, v___x_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_array_get_size(v_buckets_x27_1289_);
v___x_1295_ = lean_nat_dec_le(v___x_1293_, v___x_1294_);
lean_dec(v___x_1293_);
if (v___x_1295_ == 0)
{
lean_object* v_val_1296_; lean_object* v___x_1298_; 
v_val_1296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_buckets_x27_1289_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_val_1296_);
lean_ctor_set(v___x_1269_, 0, v_size_x27_1287_);
v___x_1298_ = v___x_1269_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_size_x27_1287_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_val_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v___x_1301_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_buckets_x27_1289_);
lean_ctor_set(v___x_1269_, 0, v_size_x27_1287_);
v___x_1301_ = v___x_1269_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_size_x27_1287_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_buckets_x27_1289_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v___x_1303_; lean_object* v_buckets_x27_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_inc(v_bkt_1284_);
v___x_1303_ = lean_box(0);
v_buckets_x27_1304_ = lean_array_uset(v_buckets_1267_, v___x_1283_, v___x_1303_);
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1264_, v_b_1265_, v_bkt_1284_);
v___x_1306_ = lean_array_uset(v_buckets_x27_1304_, v___x_1283_, v___x_1305_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___x_1306_);
v___x_1308_ = v___x_1269_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_size_1266_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(lean_object* v_a_1311_, lean_object* v_x_1312_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 0)
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
else
{
lean_object* v_key_1314_; lean_object* v_value_1315_; lean_object* v_tail_1316_; uint8_t v___x_1317_; 
v_key_1314_ = lean_ctor_get(v_x_1312_, 0);
v_value_1315_ = lean_ctor_get(v_x_1312_, 1);
v_tail_1316_ = lean_ctor_get(v_x_1312_, 2);
v___x_1317_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1314_, v_a_1311_);
if (v___x_1317_ == 0)
{
v_x_1312_ = v_tail_1316_;
goto _start;
}
else
{
lean_object* v___x_1319_; 
lean_inc(v_value_1315_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_value_1315_);
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg___boxed(lean_object* v_a_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1320_, v_x_1321_);
lean_dec(v_x_1321_);
lean_dec_ref(v_a_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object* v_m_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_buckets_1325_; lean_object* v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v_fold_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_buckets_1325_ = lean_ctor_get(v_m_1323_, 1);
v___x_1326_ = lean_array_get_size(v_buckets_1325_);
v___x_1327_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1324_);
v___x_1328_ = 32ULL;
v___x_1329_ = lean_uint64_shift_right(v___x_1327_, v___x_1328_);
v_fold_1330_ = lean_uint64_xor(v___x_1327_, v___x_1329_);
v___x_1331_ = 16ULL;
v___x_1332_ = lean_uint64_shift_right(v_fold_1330_, v___x_1331_);
v___x_1333_ = lean_uint64_xor(v_fold_1330_, v___x_1332_);
v___x_1334_ = lean_uint64_to_usize(v___x_1333_);
v___x_1335_ = lean_usize_of_nat(v___x_1326_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_sub(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_usize_land(v___x_1334_, v___x_1337_);
v___x_1339_ = lean_array_uget_borrowed(v_buckets_1325_, v___x_1338_);
v___x_1340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1324_, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object* v_m_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1341_, v_a_1342_);
lean_dec_ref(v_a_1342_);
lean_dec_ref(v_m_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(uint8_t v___x_1344_, uint8_t v___x_1345_, lean_object* v_as_1346_, size_t v_i_1347_, size_t v_stop_1348_, lean_object* v_b_1349_){
_start:
{
lean_object* v___y_1351_; uint8_t v___x_1355_; 
v___x_1355_ = lean_usize_dec_eq(v_i_1347_, v_stop_1348_);
if (v___x_1355_ == 0)
{
lean_object* v_fst_1356_; uint8_t v___x_1357_; 
v_fst_1356_ = lean_ctor_get(v_b_1349_, 0);
v___x_1357_ = lean_unbox(v_fst_1356_);
if (v___x_1357_ == 0)
{
lean_object* v_snd_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
v_snd_1358_ = lean_ctor_get(v_b_1349_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_b_1349_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v_b_1349_, 0);
lean_dec(v_unused_1367_);
v___x_1360_ = v_b_1349_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_snd_1358_);
lean_dec(v_b_1349_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_box(v___x_1344_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1358_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v___y_1351_ = v___x_1364_;
goto v___jp_1350_;
}
}
}
else
{
lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1378_; 
v_snd_1368_ = lean_ctor_get(v_b_1349_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_b_1349_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_b_1349_, 0);
lean_dec(v_unused_1379_);
v___x_1370_ = v_b_1349_;
v_isShared_1371_ = v_isSharedCheck_1378_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_dec(v_b_1349_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1378_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1372_ = lean_array_uget_borrowed(v_as_1346_, v_i_1347_);
lean_inc(v___x_1372_);
v___x_1373_ = lean_array_push(v_snd_1368_, v___x_1372_);
v___x_1374_ = lean_box(v___x_1345_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1373_);
lean_ctor_set(v___x_1370_, 0, v___x_1374_);
v___x_1376_ = v___x_1370_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1373_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
v___y_1351_ = v___x_1376_;
goto v___jp_1350_;
}
}
}
}
else
{
return v_b_1349_;
}
v___jp_1350_:
{
size_t v___x_1352_; size_t v___x_1353_; 
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1347_, v___x_1352_);
v_i_1347_ = v___x_1353_;
v_b_1349_ = v___y_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_stop_1384_, lean_object* v_b_1385_){
_start:
{
uint8_t v___x_9236__boxed_1386_; uint8_t v___x_9237__boxed_1387_; size_t v_i_boxed_1388_; size_t v_stop_boxed_1389_; lean_object* v_res_1390_; 
v___x_9236__boxed_1386_ = lean_unbox(v___x_1380_);
v___x_9237__boxed_1387_ = lean_unbox(v___x_1381_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_stop_boxed_1389_ = lean_unbox_usize(v_stop_1384_);
lean_dec(v_stop_1384_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_9236__boxed_1386_, v___x_9237__boxed_1387_, v_as_1382_, v_i_boxed_1388_, v_stop_boxed_1389_, v_b_1385_);
lean_dec_ref(v_as_1382_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_bs_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_bs_1393_);
return v___x_1395_;
}
else
{
lean_object* v_v_1396_; lean_object* v___x_1397_; lean_object* v_bs_x27_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v_v_1396_ = lean_array_uget(v_bs_1393_, v_i_1392_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v_bs_x27_1398_ = lean_array_uset(v_bs_1393_, v_i_1392_, v___x_1397_);
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_add(v_i_1392_, v___x_1399_);
v___x_1401_ = lean_array_uset(v_bs_x27_1398_, v_i_1392_, v_v_1396_);
v_i_1392_ = v___x_1400_;
v_bs_1393_ = v___x_1401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object* v_sz_1403_, lean_object* v_i_1404_, lean_object* v_bs_1405_){
_start:
{
size_t v_sz_boxed_1406_; size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_sz_boxed_1406_ = lean_unbox_usize(v_sz_1403_);
lean_dec(v_sz_1403_);
v_i_boxed_1407_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_boxed_1406_, v_i_boxed_1407_, v_bs_1405_);
return v_res_1408_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4));
v___x_1419_ = l_Lean_mkConst(v___x_1418_, v___x_1417_);
return v___x_1419_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(lean_object* v_stx_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_1440_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1675_; 
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1572_, 0);
lean_dec(v_unused_1676_);
v___x_1574_ = v___x_1572_;
v_isShared_1575_ = v_isSharedCheck_1675_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v___x_1572_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1675_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
lean_inc(v_stx_1439_);
v___x_1577_ = l_Lean_Syntax_isOfKind(v_stx_1439_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_del_object(v___x_1574_);
lean_dec(v_stx_1439_);
v___x_1578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1609_; lean_object* v_args_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___x_1637_; lean_object* v_variantId_x3f_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1666_ = l_Lean_Syntax_getArg(v_stx_1439_, v___x_1637_);
v___x_1667_ = l_Lean_Syntax_isNone(v___x_1666_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; 
lean_inc(v___x_1666_);
v___x_1668_ = l_Lean_Syntax_matchesNull(v___x_1666_, v___x_1637_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec(v___x_1666_);
lean_del_object(v___x_1574_);
lean_dec(v_stx_1439_);
v___x_1669_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = l_Lean_Syntax_getArg(v___x_1666_, v___x_1579_);
lean_dec(v___x_1666_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1670_);
v___x_1672_ = v___x_1574_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
v_variantId_x3f_1639_ = v___x_1672_;
v___y_1640_ = v___y_1440_;
v___y_1641_ = v___y_1441_;
v___y_1642_ = v___y_1442_;
v___y_1643_ = v___y_1443_;
v___y_1644_ = v___y_1444_;
v___y_1645_ = v___y_1445_;
v___y_1646_ = v___y_1446_;
v___y_1647_ = v___y_1447_;
goto v___jp_1638_;
}
}
}
else
{
lean_object* v___x_1674_; 
lean_dec(v___x_1666_);
lean_del_object(v___x_1574_);
v___x_1674_ = lean_box(0);
v_variantId_x3f_1639_ = v___x_1674_;
v___y_1640_ = v___y_1440_;
v___y_1641_ = v___y_1441_;
v___y_1642_ = v___y_1442_;
v___y_1643_ = v___y_1443_;
v___y_1644_ = v___y_1444_;
v___y_1645_ = v___y_1445_;
v___y_1646_ = v___y_1446_;
v___y_1647_ = v___y_1447_;
goto v___jp_1638_;
}
v___jp_1580_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v___y_1586_, v___y_1581_, v___y_1585_, v___y_1589_, v___y_1588_, v___y_1583_, v___y_1587_, v___y_1584_, v___y_1582_);
lean_dec(v___y_1586_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_cache_1595_; lean_object* v_dsimpState_1596_; lean_object* v___x_1597_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc_n(v_a_1592_, 2);
lean_dec_ref_known(v___x_1591_, 1);
lean_inc(v___y_1590_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___y_1590_);
lean_ctor_set(v___x_1593_, 1, v_a_1592_);
v___x_1594_ = lean_st_ref_get(v___y_1585_);
v_cache_1595_ = lean_ctor_get(v___x_1594_, 3);
lean_inc_ref(v_cache_1595_);
lean_dec(v___x_1594_);
v_dsimpState_1596_ = lean_ctor_get(v_cache_1595_, 3);
lean_inc_ref(v_dsimpState_1596_);
lean_dec_ref(v_cache_1595_);
v___x_1597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_dsimpState_1596_, v___x_1593_);
lean_dec_ref(v_dsimpState_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14);
v___y_1450_ = v___y_1581_;
v___y_1451_ = v___y_1582_;
v___y_1452_ = v___y_1583_;
v___y_1453_ = v___y_1584_;
v___y_1454_ = v_a_1592_;
v___y_1455_ = v___y_1585_;
v___y_1456_ = v___y_1587_;
v___y_1457_ = v___x_1593_;
v___y_1458_ = v___y_1588_;
v___y_1459_ = v___y_1589_;
v___y_1460_ = v___y_1590_;
v___y_1461_ = v___x_1598_;
goto v___jp_1449_;
}
else
{
lean_object* v_val_1599_; 
v_val_1599_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_val_1599_);
lean_dec_ref_known(v___x_1597_, 1);
v___y_1450_ = v___y_1581_;
v___y_1451_ = v___y_1582_;
v___y_1452_ = v___y_1583_;
v___y_1453_ = v___y_1584_;
v___y_1454_ = v_a_1592_;
v___y_1455_ = v___y_1585_;
v___y_1456_ = v___y_1587_;
v___y_1457_ = v___x_1593_;
v___y_1458_ = v___y_1588_;
v___y_1459_ = v___y_1589_;
v___y_1460_ = v___y_1590_;
v___y_1461_ = v_val_1599_;
goto v___jp_1449_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v___y_1590_);
v_a_1600_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1591_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1591_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
v___jp_1608_:
{
if (lean_obj_tag(v___y_1609_) == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_box(0);
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1618_;
v___y_1583_ = v___y_1615_;
v___y_1584_ = v___y_1617_;
v___y_1585_ = v___y_1612_;
v___y_1586_ = v_args_1610_;
v___y_1587_ = v___y_1616_;
v___y_1588_ = v___y_1614_;
v___y_1589_ = v___y_1613_;
v___y_1590_ = v___x_1619_;
goto v___jp_1580_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
v_val_1620_ = lean_ctor_get(v___y_1609_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v___y_1609_, 1);
v___x_1621_ = l_Lean_TSyntax_getId(v_val_1620_);
lean_dec(v_val_1620_);
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1618_;
v___y_1583_ = v___y_1615_;
v___y_1584_ = v___y_1617_;
v___y_1585_ = v___y_1612_;
v___y_1586_ = v_args_1610_;
v___y_1587_ = v___y_1616_;
v___y_1588_ = v___y_1614_;
v___y_1589_ = v___y_1613_;
v___y_1590_ = v___x_1621_;
goto v___jp_1580_;
}
}
v___jp_1622_:
{
size_t v_sz_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
v_sz_1633_ = lean_array_size(v___y_1632_);
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_1633_, v___x_1634_, v___y_1632_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec(v___y_1623_);
v___x_1636_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1636_;
}
else
{
v___y_1609_ = v___y_1623_;
v_args_1610_ = v___x_1635_;
v___y_1611_ = v___y_1629_;
v___y_1612_ = v___y_1631_;
v___y_1613_ = v___y_1625_;
v___y_1614_ = v___y_1627_;
v___y_1615_ = v___y_1626_;
v___y_1616_ = v___y_1630_;
v___y_1617_ = v___y_1628_;
v___y_1618_ = v___y_1624_;
goto v___jp_1608_;
}
}
v___jp_1638_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = lean_unsigned_to_nat(2u);
v___x_1649_ = l_Lean_Syntax_getArg(v_stx_1439_, v___x_1648_);
lean_dec(v_stx_1439_);
v___x_1650_ = l_Lean_Syntax_isNone(v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1649_);
v___x_1652_ = l_Lean_Syntax_matchesNull(v___x_1649_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec(v___x_1649_);
lean_dec(v_variantId_x3f_1639_);
v___x_1653_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1654_ = l_Lean_Syntax_getArg(v___x_1649_, v___x_1637_);
lean_dec(v___x_1649_);
v___x_1655_ = l_Lean_Syntax_getArgs(v___x_1654_);
lean_dec(v___x_1654_);
v___x_1656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15));
v___x_1657_ = lean_array_get_size(v___x_1655_);
v___x_1658_ = lean_nat_dec_lt(v___x_1579_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec_ref(v___x_1655_);
v___y_1623_ = v_variantId_x3f_1639_;
v___y_1624_ = v___y_1647_;
v___y_1625_ = v___y_1642_;
v___y_1626_ = v___y_1644_;
v___y_1627_ = v___y_1643_;
v___y_1628_ = v___y_1646_;
v___y_1629_ = v___y_1640_;
v___y_1630_ = v___y_1645_;
v___y_1631_ = v___y_1641_;
v___y_1632_ = v___x_1656_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; lean_object* v_snd_1664_; 
v___x_1659_ = lean_box(v___x_1658_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set(v___x_1660_, 1, v___x_1656_);
v___x_1661_ = ((size_t)0ULL);
v___x_1662_ = lean_usize_of_nat(v___x_1657_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_1652_, v___x_1650_, v___x_1655_, v___x_1661_, v___x_1662_, v___x_1660_);
lean_dec_ref(v___x_1655_);
v_snd_1664_ = lean_ctor_get(v___x_1663_, 1);
lean_inc(v_snd_1664_);
lean_dec_ref(v___x_1663_);
v___y_1623_ = v_variantId_x3f_1639_;
v___y_1624_ = v___y_1647_;
v___y_1625_ = v___y_1642_;
v___y_1626_ = v___y_1644_;
v___y_1627_ = v___y_1643_;
v___y_1628_ = v___y_1646_;
v___y_1629_ = v___y_1640_;
v___y_1630_ = v___y_1645_;
v___y_1631_ = v___y_1641_;
v___y_1632_ = v_snd_1664_;
goto v___jp_1622_;
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v___x_1649_);
v___x_1665_ = lean_box(0);
v___y_1609_ = v_variantId_x3f_1639_;
v_args_1610_ = v___x_1665_;
v___y_1611_ = v___y_1640_;
v___y_1612_ = v___y_1641_;
v___y_1613_ = v___y_1642_;
v___y_1614_ = v___y_1643_;
v___y_1615_ = v___y_1644_;
v___y_1616_ = v___y_1645_;
v___y_1617_ = v___y_1646_;
v___y_1618_ = v___y_1647_;
goto v___jp_1608_;
}
}
}
}
}
else
{
lean_dec(v_stx_1439_);
return v___x_1572_;
}
v___jp_1449_:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v___y_1460_, v___y_1454_, v___y_1450_, v___y_1455_, v___y_1459_, v___y_1458_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_fst_1464_; lean_object* v_snd_1465_; lean_object* v___x_1466_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v_fst_1464_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_fst_1464_);
v_snd_1465_ = lean_ctor_get(v_a_1463_, 1);
lean_inc(v_snd_1465_);
lean_dec(v_a_1463_);
v___x_1466_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1455_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_toGoalState_1468_; lean_object* v_mvarId_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1555_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_toGoalState_1468_ = lean_ctor_get(v_a_1467_, 0);
v_mvarId_1469_ = lean_ctor_get(v_a_1467_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_a_1467_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1471_ = v_a_1467_;
v_isShared_1472_ = v_isSharedCheck_1555_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_mvarId_1469_);
lean_inc(v_toGoalState_1468_);
lean_dec(v_a_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1555_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc_n(v_mvarId_1469_, 2);
v___f_1473_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1473_, 0, v_mvarId_1469_);
lean_closure_set(v___f_1473_, 1, v_fst_1464_);
lean_closure_set(v___f_1473_, 2, v_snd_1465_);
lean_closure_set(v___f_1473_, 3, v___y_1461_);
v___x_1474_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed), 13, 3);
lean_closure_set(v___x_1474_, 0, lean_box(0));
lean_closure_set(v___x_1474_, 1, v_mvarId_1469_);
lean_closure_set(v___x_1474_, 2, v___f_1473_);
v___x_1475_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1474_, v___y_1450_, v___y_1455_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_fst_1477_; lean_object* v_snd_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1546_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v_fst_1477_ = lean_ctor_get(v_a_1476_, 0);
v_snd_1478_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1480_ = v_a_1476_;
v_isShared_1481_ = v_isSharedCheck_1546_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snd_1478_);
lean_inc(v_fst_1477_);
lean_dec(v_a_1476_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1546_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v_cache_1483_; lean_object* v_symState_1484_; lean_object* v_grindState_1485_; lean_object* v_goals_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1545_; 
v___x_1482_ = lean_st_ref_take(v___y_1455_);
v_cache_1483_ = lean_ctor_get(v___x_1482_, 3);
v_symState_1484_ = lean_ctor_get(v___x_1482_, 0);
v_grindState_1485_ = lean_ctor_get(v___x_1482_, 1);
v_goals_1486_ = lean_ctor_get(v___x_1482_, 2);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1488_ = v___x_1482_;
v_isShared_1489_ = v_isSharedCheck_1545_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_cache_1483_);
lean_inc(v_goals_1486_);
lean_inc(v_grindState_1485_);
lean_inc(v_symState_1484_);
lean_dec(v___x_1482_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1545_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_backwardRuleName_1490_; lean_object* v_backwardRuleSyntax_1491_; lean_object* v_simpState_1492_; lean_object* v_dsimpState_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1544_; 
v_backwardRuleName_1490_ = lean_ctor_get(v_cache_1483_, 0);
v_backwardRuleSyntax_1491_ = lean_ctor_get(v_cache_1483_, 1);
v_simpState_1492_ = lean_ctor_get(v_cache_1483_, 2);
v_dsimpState_1493_ = lean_ctor_get(v_cache_1483_, 3);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_cache_1483_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1495_ = v_cache_1483_;
v_isShared_1496_ = v_isSharedCheck_1544_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_dsimpState_1493_);
lean_inc(v_simpState_1492_);
lean_inc(v_backwardRuleSyntax_1491_);
lean_inc(v_backwardRuleName_1490_);
lean_dec(v_cache_1483_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1544_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_dsimpState_1493_, v___y_1457_, v_snd_1478_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 3, v___x_1497_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_backwardRuleName_1490_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_backwardRuleSyntax_1491_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_simpState_1492_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 3, v___x_1499_);
v___x_1501_ = v___x_1488_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_symState_1484_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_grindState_1485_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_goals_1486_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_st_ref_put(v___y_1455_, v___x_1501_);
if (lean_obj_tag(v_fst_1477_) == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref_known(v_fst_1477_, 0);
lean_del_object(v___x_1480_);
lean_del_object(v___x_1471_);
lean_dec(v_mvarId_1469_);
lean_dec_ref(v_toGoalState_1468_);
v___x_1503_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1);
v___x_1504_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___redArg(v___x_1503_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
return v___x_1504_;
}
else
{
lean_object* v_e_x27_1505_; uint8_t v___x_1506_; 
v_e_x27_1505_ = lean_ctor_get(v_fst_1477_, 0);
lean_inc_ref_n(v_e_x27_1505_, 2);
lean_dec_ref_known(v_fst_1477_, 1);
v___x_1506_ = l_Lean_Expr_isTrue(v_e_x27_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_inc(v_mvarId_1469_);
v___x_1507_ = l_Lean_MVarId_getDecl(v_mvarId_1469_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v_userName_1509_; lean_object* v___x_1510_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v_userName_1509_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_userName_1509_);
lean_dec(v_a_1508_);
v___x_1510_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_1505_, v_userName_1509_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_n(v_a_1511_, 2);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1469_, v_a_1511_, v___y_1456_);
lean_dec_ref(v___x_1512_);
v___x_1513_ = l_Lean_Expr_mvarId_x21(v_a_1511_);
lean_dec(v_a_1511_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1513_);
v___x_1515_ = v___x_1471_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_toGoalState_1468_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 1);
lean_ctor_set(v___x_1480_, 1, v___x_1516_);
lean_ctor_set(v___x_1480_, 0, v___x_1515_);
v___x_1518_ = v___x_1480_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1518_, v___y_1455_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_1480_);
lean_del_object(v___x_1471_);
lean_dec(v_mvarId_1469_);
lean_dec_ref(v_toGoalState_1468_);
v_a_1522_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1510_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1510_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_e_x27_1505_);
lean_del_object(v___x_1480_);
lean_del_object(v___x_1471_);
lean_dec(v_mvarId_1469_);
lean_dec_ref(v_toGoalState_1468_);
v_a_1530_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1507_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1507_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec_ref(v_e_x27_1505_);
lean_del_object(v___x_1480_);
lean_del_object(v___x_1471_);
lean_dec_ref(v_toGoalState_1468_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5);
v___x_1540_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1469_, v___x_1539_, v___y_1456_);
lean_dec_ref(v___x_1540_);
v___x_1541_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1538_, v___y_1455_, v___y_1452_, v___y_1456_, v___y_1453_, v___y_1451_);
return v___x_1541_;
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
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_del_object(v___x_1471_);
lean_dec(v_mvarId_1469_);
lean_dec_ref(v_toGoalState_1468_);
lean_dec_ref(v___y_1457_);
v_a_1547_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1475_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1475_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_snd_1465_);
lean_dec(v_fst_1464_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v___y_1457_);
v_a_1556_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1466_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1466_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v___y_1461_);
lean_dec_ref(v___y_1457_);
v_a_1564_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1462_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1462_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed(lean_object* v_stx_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(v_stx_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(lean_object* v_stx_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___f_1698_; lean_object* v___x_1699_; 
v___f_1698_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1698_, 0, v_stx_1688_);
v___x_1699_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1698_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed(lean_object* v_stx_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(v_stx_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object* v_00_u03b2_1711_, lean_object* v_m_1712_, lean_object* v_a_1713_, lean_object* v_b_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_m_1712_, v_a_1713_, v_b_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object* v_mvarId_1716_, lean_object* v_val_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1716_, v_val_1717_, v___y_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object* v_mvarId_1728_, lean_object* v_val_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(v_mvarId_1728_, v_val_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object* v_00_u03b2_1740_, lean_object* v_m_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1741_, v_a_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object* v_00_u03b2_1744_, lean_object* v_m_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(v_00_u03b2_1744_, v_m_1745_, v_a_1746_);
lean_dec_ref(v_a_1746_);
lean_dec_ref(v_m_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object* v_00_u03b2_1748_, lean_object* v_a_1749_, lean_object* v_x_1750_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1749_, v_x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1752_, lean_object* v_a_1753_, lean_object* v_x_1754_){
_start:
{
uint8_t v_res_1755_; lean_object* v_r_1756_; 
v_res_1755_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(v_00_u03b2_1752_, v_a_1753_, v_x_1754_);
lean_dec(v_x_1754_);
lean_dec_ref(v_a_1753_);
v_r_1756_ = lean_box(v_res_1755_);
return v_r_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3(lean_object* v_00_u03b2_1757_, lean_object* v_data_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_data_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4(lean_object* v_00_u03b2_1760_, lean_object* v_a_1761_, lean_object* v_b_1762_, lean_object* v_x_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1761_, v_b_1762_, v_x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6(lean_object* v_00_u03b2_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_x_1766_, v_x_1767_, v_x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(lean_object* v_00_u03b2_1770_, lean_object* v_a_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1771_, v_x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1774_, lean_object* v_a_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(v_00_u03b2_1774_, v_a_1775_, v_x_1776_);
lean_dec(v_x_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1778_, lean_object* v_i_1779_, lean_object* v_source_1780_, lean_object* v_target_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v_i_1779_, v_source_1780_, v_target_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1783_, lean_object* v_x_1784_, size_t v_x_1785_, size_t v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1784_, v_x_1785_, v_x_1786_, v_x_1787_, v_x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_){
_start:
{
size_t v_x_9931__boxed_1796_; size_t v_x_9932__boxed_1797_; lean_object* v_res_1798_; 
v_x_9931__boxed_1796_ = lean_unbox_usize(v_x_1792_);
lean_dec(v_x_1792_);
v_x_9932__boxed_1797_ = lean_unbox_usize(v_x_1793_);
lean_dec(v_x_1793_);
v_res_1798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(v_00_u03b2_1790_, v_x_1791_, v_x_9931__boxed_1796_, v_x_9932__boxed_1797_, v_x_1794_, v_x_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_x_1800_, v_x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1803_, lean_object* v_n_1804_, lean_object* v_k_1805_, lean_object* v_v_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v_n_1804_, v_k_1805_, v_v_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1808_, size_t v_depth_1809_, lean_object* v_keys_1810_, lean_object* v_vals_1811_, lean_object* v_heq_1812_, lean_object* v_i_1813_, lean_object* v_entries_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_1809_, v_keys_1810_, v_vals_1811_, v_i_1813_, v_entries_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1816_, lean_object* v_depth_1817_, lean_object* v_keys_1818_, lean_object* v_vals_1819_, lean_object* v_heq_1820_, lean_object* v_i_1821_, lean_object* v_entries_1822_){
_start:
{
size_t v_depth_boxed_1823_; lean_object* v_res_1824_; 
v_depth_boxed_1823_ = lean_unbox_usize(v_depth_1817_);
lean_dec(v_depth_1817_);
v_res_1824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(v_00_u03b2_1816_, v_depth_boxed_1823_, v_keys_1818_, v_vals_1819_, v_heq_1820_, v_i_1821_, v_entries_1822_);
lean_dec_ref(v_vals_1819_);
lean_dec_ref(v_keys_1818_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15(lean_object* v_00_u03b2_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_x_1826_, v_x_1827_, v_x_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1(){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1872_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15));
v___x_1875_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed), 10, 0);
v___x_1876_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1872_, v___x_1873_, v___x_1874_, v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___boxed(lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
return v_res_1878_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
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
lean_object* initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
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
