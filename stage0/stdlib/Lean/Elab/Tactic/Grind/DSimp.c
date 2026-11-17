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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint64_t l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__6_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__7 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__7_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__8 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__0 = (const lean_object*)&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__0_value;
static const lean_string_object l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__1 = (const lean_object*)&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__1_value;
static const lean_string_object l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__2 = (const lean_object*)&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)(((size_t)(65536) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_evalGround___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__2_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__4_value;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2_spec__3(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2_spec__3___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2_spec__3(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2_spec__3(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_instMonadEIO___redArg();
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(lean_object* v_msg_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_toApplicative_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_192_; 
v___x_69_ = lean_obj_once(&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__0, &l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__0);
v___x_70_ = l_StateRefT_x27_instMonad___redArg(v___x_69_);
v_toApplicative_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v___x_70_, 1);
lean_dec(v_unused_193_);
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_192_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_toApplicative_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_192_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_toFunctor_75_; lean_object* v_toSeq_76_; lean_object* v_toSeqLeft_77_; lean_object* v_toSeqRight_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_190_; 
v_toFunctor_75_ = lean_ctor_get(v_toApplicative_71_, 0);
v_toSeq_76_ = lean_ctor_get(v_toApplicative_71_, 2);
v_toSeqLeft_77_ = lean_ctor_get(v_toApplicative_71_, 3);
v_toSeqRight_78_ = lean_ctor_get(v_toApplicative_71_, 4);
v_isSharedCheck_190_ = !lean_is_exclusive(v_toApplicative_71_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v_toApplicative_71_, 1);
lean_dec(v_unused_191_);
v___x_80_ = v_toApplicative_71_;
v_isShared_81_ = v_isSharedCheck_190_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_toSeqRight_78_);
lean_inc(v_toSeqLeft_77_);
lean_inc(v_toSeq_76_);
lean_inc(v_toFunctor_75_);
lean_dec(v_toApplicative_71_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_190_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___x_91_; 
v___f_82_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__1));
v___f_83_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_75_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_84_, 0, v_toFunctor_75_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toFunctor_75_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___f_84_);
lean_ctor_set(v___x_86_, 1, v___f_85_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeqRight_78_);
v___f_88_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_88_, 0, v_toSeqLeft_77_);
v___f_89_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_89_, 0, v_toSeq_76_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 4, v___f_87_);
lean_ctor_set(v___x_80_, 3, v___f_88_);
lean_ctor_set(v___x_80_, 2, v___f_89_);
lean_ctor_set(v___x_80_, 1, v___f_82_);
lean_ctor_set(v___x_80_, 0, v___x_86_);
v___x_91_ = v___x_80_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___f_82_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v___f_89_);
lean_ctor_set(v_reuseFailAlloc_189_, 3, v___f_88_);
lean_ctor_set(v_reuseFailAlloc_189_, 4, v___f_87_);
v___x_91_ = v_reuseFailAlloc_189_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___f_83_);
lean_ctor_set(v___x_73_, 0, v___x_91_);
v___x_93_ = v___x_73_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___f_83_);
v___x_93_ = v_reuseFailAlloc_188_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v_toApplicative_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_186_; 
v___x_94_ = l_StateRefT_x27_instMonad___redArg(v___x_93_);
v_toApplicative_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v___x_94_, 1);
lean_dec(v_unused_187_);
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_186_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_toApplicative_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_186_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_toFunctor_99_; lean_object* v_toSeq_100_; lean_object* v_toSeqLeft_101_; lean_object* v_toSeqRight_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_184_; 
v_toFunctor_99_ = lean_ctor_get(v_toApplicative_95_, 0);
v_toSeq_100_ = lean_ctor_get(v_toApplicative_95_, 2);
v_toSeqLeft_101_ = lean_ctor_get(v_toApplicative_95_, 3);
v_toSeqRight_102_ = lean_ctor_get(v_toApplicative_95_, 4);
v_isSharedCheck_184_ = !lean_is_exclusive(v_toApplicative_95_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v_toApplicative_95_, 1);
lean_dec(v_unused_185_);
v___x_104_ = v_toApplicative_95_;
v_isShared_105_ = v_isSharedCheck_184_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_toSeqRight_102_);
lean_inc(v_toSeqLeft_101_);
lean_inc(v_toSeq_100_);
lean_inc(v_toFunctor_99_);
lean_dec(v_toApplicative_95_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_184_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_115_; 
v___f_106_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__3));
v___f_107_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_99_);
v___f_108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_108_, 0, v_toFunctor_99_);
v___f_109_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_109_, 0, v_toFunctor_99_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___f_108_);
lean_ctor_set(v___x_110_, 1, v___f_109_);
v___f_111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_111_, 0, v_toSeqRight_102_);
v___f_112_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_112_, 0, v_toSeqLeft_101_);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_113_, 0, v_toSeq_100_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 4, v___f_111_);
lean_ctor_set(v___x_104_, 3, v___f_112_);
lean_ctor_set(v___x_104_, 2, v___f_113_);
lean_ctor_set(v___x_104_, 1, v___f_106_);
lean_ctor_set(v___x_104_, 0, v___x_110_);
v___x_115_ = v___x_104_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___f_106_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v___f_113_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v___f_112_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v___f_111_);
v___x_115_ = v_reuseFailAlloc_183_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_117_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___f_107_);
lean_ctor_set(v___x_97_, 0, v___x_115_);
v___x_117_ = v___x_97_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___f_107_);
v___x_117_ = v_reuseFailAlloc_182_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v_toApplicative_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_180_; 
v___x_118_ = l_StateRefT_x27_instMonad___redArg(v___x_117_);
v_toApplicative_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v___x_118_, 1);
lean_dec(v_unused_181_);
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_180_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_toApplicative_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_180_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_toFunctor_123_; lean_object* v_toSeq_124_; lean_object* v_toSeqLeft_125_; lean_object* v_toSeqRight_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_178_; 
v_toFunctor_123_ = lean_ctor_get(v_toApplicative_119_, 0);
v_toSeq_124_ = lean_ctor_get(v_toApplicative_119_, 2);
v_toSeqLeft_125_ = lean_ctor_get(v_toApplicative_119_, 3);
v_toSeqRight_126_ = lean_ctor_get(v_toApplicative_119_, 4);
v_isSharedCheck_178_ = !lean_is_exclusive(v_toApplicative_119_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; 
v_unused_179_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_dec(v_unused_179_);
v___x_128_ = v_toApplicative_119_;
v_isShared_129_ = v_isSharedCheck_178_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_toSeqRight_126_);
lean_inc(v_toSeqLeft_125_);
lean_inc(v_toSeq_124_);
lean_inc(v_toFunctor_123_);
lean_dec(v_toApplicative_119_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_178_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___x_139_; 
v___f_130_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__5));
v___f_131_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__6));
lean_inc_ref(v_toFunctor_123_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_132_, 0, v_toFunctor_123_);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_133_, 0, v_toFunctor_123_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___f_132_);
lean_ctor_set(v___x_134_, 1, v___f_133_);
v___f_135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_135_, 0, v_toSeqRight_126_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeqLeft_125_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_137_, 0, v_toSeq_124_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 4, v___f_135_);
lean_ctor_set(v___x_128_, 3, v___f_136_);
lean_ctor_set(v___x_128_, 2, v___f_137_);
lean_ctor_set(v___x_128_, 1, v___f_130_);
lean_ctor_set(v___x_128_, 0, v___x_134_);
v___x_139_ = v___x_128_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___f_130_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v___f_136_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v___f_135_);
v___x_139_ = v_reuseFailAlloc_177_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___f_131_);
lean_ctor_set(v___x_121_, 0, v___x_139_);
v___x_141_ = v___x_121_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___f_131_);
v___x_141_ = v_reuseFailAlloc_176_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v_toApplicative_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_174_; 
v___x_142_ = l_StateRefT_x27_instMonad___redArg(v___x_141_);
v_toApplicative_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_142_, 1);
lean_dec(v_unused_175_);
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_174_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_toApplicative_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_174_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_toFunctor_147_; lean_object* v_toSeq_148_; lean_object* v_toSeqLeft_149_; lean_object* v_toSeqRight_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_172_; 
v_toFunctor_147_ = lean_ctor_get(v_toApplicative_143_, 0);
v_toSeq_148_ = lean_ctor_get(v_toApplicative_143_, 2);
v_toSeqLeft_149_ = lean_ctor_get(v_toApplicative_143_, 3);
v_toSeqRight_150_ = lean_ctor_get(v_toApplicative_143_, 4);
v_isSharedCheck_172_ = !lean_is_exclusive(v_toApplicative_143_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_dec(v_unused_173_);
v___x_152_ = v_toApplicative_143_;
v_isShared_153_ = v_isSharedCheck_172_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_toSeqRight_150_);
lean_inc(v_toSeqLeft_149_);
lean_inc(v_toSeq_148_);
lean_inc(v_toFunctor_147_);
lean_dec(v_toApplicative_143_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_172_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___x_163_; 
v___f_154_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__7));
v___f_155_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___closed__8));
lean_inc_ref(v_toFunctor_147_);
v___f_156_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_156_, 0, v_toFunctor_147_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_157_, 0, v_toFunctor_147_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___f_156_);
lean_ctor_set(v___x_158_, 1, v___f_157_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_159_, 0, v_toSeqRight_150_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_160_, 0, v_toSeqLeft_149_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeq_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v___f_159_);
lean_ctor_set(v___x_152_, 3, v___f_160_);
lean_ctor_set(v___x_152_, 2, v___f_161_);
lean_ctor_set(v___x_152_, 1, v___f_154_);
lean_ctor_set(v___x_152_, 0, v___x_158_);
v___x_163_ = v___x_152_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___f_154_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v___f_161_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v___f_160_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v___f_159_);
v___x_163_ = v_reuseFailAlloc_171_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___f_155_);
lean_ctor_set(v___x_145_, 0, v___x_163_);
v___x_165_ = v___x_145_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___f_155_);
v___x_165_ = v_reuseFailAlloc_170_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_4468__overap_168_; lean_object* v___x_169_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_instInhabitedOfMonad___redArg(v___x_165_, v___x_166_);
v___x_4468__overap_168_ = lean_panic_fn_borrowed(v___x_167_, v_msg_59_);
lean_dec(v___x_167_);
lean_inc(v___y_67_);
lean_inc_ref(v___y_66_);
lean_inc(v___y_65_);
lean_inc_ref(v___y_64_);
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
v___x_169_ = lean_apply_9(v___x_4468__overap_168_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, lean_box(0));
return v___x_169_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0___boxed(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_208_ = ((lean_object*)(l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__2));
v___x_209_ = lean_unsigned_to_nat(11u);
v___x_210_ = lean_unsigned_to_nat(115u);
v___x_211_ = ((lean_object*)(l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__1));
v___x_212_ = ((lean_object*)(l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__0));
v___x_213_ = l_mkPanicMessageWithDecl(v___x_212_, v___x_211_, v___x_210_, v___x_209_, v___x_208_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(lean_object* v_constName_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; lean_object* v_env_228_; uint8_t v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_st_ref_get(v___y_222_);
v_env_228_ = lean_ctor_get(v___x_224_, 0);
lean_inc_ref(v_env_228_);
lean_dec(v___x_224_);
v___x_229_ = 0;
v___x_230_ = l_Lean_Environment_findAsync_x3f(v_env_228_, v_constName_214_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 1)
{
lean_object* v_val_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_250_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_250_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_250_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_val_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_250_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v_kind_235_; 
v_kind_235_ = lean_ctor_get_uint8(v_val_231_, sizeof(void*)*3);
if (v_kind_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_231_);
if (lean_obj_tag(v___x_236_) == 1)
{
lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_247_; 
v_val_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_247_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_247_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_247_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v_val_237_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_val_237_);
v___x_242_ = v_reuseFailAlloc_246_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 0);
lean_ctor_set(v___x_239_, 0, v___x_242_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v___x_236_);
lean_del_object(v___x_233_);
v___x_248_ = lean_obj_once(&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__3, &l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__3_once, _init_l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___closed__3);
v___x_249_ = l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0_spec__0(v___x_248_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
return v___x_249_;
}
}
else
{
lean_del_object(v___x_233_);
lean_dec(v_val_231_);
goto v___jp_225_;
}
}
}
else
{
lean_dec(v___x_230_);
goto v___jp_225_;
}
v___jp_225_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0___boxed(lean_object* v_constName_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(v_constName_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(lean_object* v___x_265_, lean_object* v_as_266_, size_t v_sz_267_, size_t v_i_268_, lean_object* v_b_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_a_280_; uint8_t v___x_284_; 
v___x_284_ = lean_usize_dec_lt(v_i_268_, v_sz_267_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v_b_269_);
return v___x_285_;
}
else
{
lean_object* v_snd_286_; lean_object* v_fst_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_357_; 
v_snd_286_ = lean_ctor_get(v_b_269_, 1);
v_fst_287_ = lean_ctor_get(v_b_269_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_b_269_);
if (v_isSharedCheck_357_ == 0)
{
v___x_289_ = v_b_269_;
v_isShared_290_ = v_isSharedCheck_357_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_snd_286_);
lean_inc(v_fst_287_);
lean_dec(v_b_269_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_357_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_fst_291_; lean_object* v_snd_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_356_; 
v_fst_291_ = lean_ctor_get(v_snd_286_, 0);
v_snd_292_ = lean_ctor_get(v_snd_286_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_snd_286_);
if (v_isSharedCheck_356_ == 0)
{
v___x_294_ = v_snd_286_;
v_isShared_295_ = v_isSharedCheck_356_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_snd_292_);
lean_inc(v_fst_291_);
lean_dec(v_snd_286_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_356_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_a_296_ = lean_array_uget_borrowed(v_as_266_, v_i_268_);
lean_inc(v_a_296_);
v___x_297_ = l_Lean_Syntax_getKind(v_a_296_);
v___x_298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___closed__1));
v___x_299_ = lean_name_eq(v___x_297_, v___x_298_);
lean_dec(v___x_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec(v_fst_291_);
v___x_300_ = lean_box(v___x_284_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_300_);
v___x_302_ = v___x_294_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_snd_292_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_302_);
v___x_304_ = v___x_289_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_fst_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
v_a_280_ = v___x_304_;
goto v___jp_279_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = l_Lean_Syntax_getId(v_a_296_);
v___x_308_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_265_, v___x_307_);
lean_dec(v___x_307_);
if (lean_obj_tag(v___x_308_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v_val_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = l_Lean_LocalDecl_fvarId(v_val_309_);
lean_dec(v_val_309_);
v___x_311_ = lean_array_push(v_fst_287_, v___x_310_);
if (v_isShared_295_ == 0)
{
v___x_313_ = v___x_294_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_fst_291_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_snd_292_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_313_);
lean_ctor_set(v___x_289_, 0, v___x_311_);
v___x_315_ = v___x_289_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
v_a_280_ = v___x_315_;
goto v___jp_279_;
}
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v___x_308_);
lean_inc(v_a_296_);
v___x_318_ = l_Lean_realizeGlobalConstNoOverload(v_a_296_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_328_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc_n(v_a_319_, 2);
lean_dec_ref_known(v___x_318_, 1);
v___x_328_ = l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__0(v_a_319_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
if (lean_obj_tag(v_a_329_) == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(1);
lean_inc(v_a_319_);
v___x_331_ = l_Lean_Linter_checkDeprecatedAt(v_a_296_, v_a_319_, v___x_330_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_dec_ref_known(v___x_331_, 1);
goto v___jp_320_;
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_a_319_);
lean_del_object(v___x_294_);
lean_dec(v_snd_292_);
lean_dec(v_fst_291_);
lean_del_object(v___x_289_);
lean_dec(v_fst_287_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_329_, 1);
goto v___jp_320_;
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_319_);
lean_del_object(v___x_294_);
lean_dec(v_snd_292_);
lean_dec(v_fst_291_);
lean_del_object(v___x_289_);
lean_dec(v_fst_287_);
v_a_340_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_328_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_328_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
v___jp_320_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_array_push(v_snd_292_, v_a_319_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v___x_321_);
v___x_323_ = v___x_294_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_fst_291_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_323_);
v___x_325_ = v___x_289_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_287_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v_a_280_ = v___x_325_;
goto v___jp_279_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_del_object(v___x_294_);
lean_dec(v_snd_292_);
lean_dec(v_fst_291_);
lean_del_object(v___x_289_);
lean_dec(v_fst_287_);
v_a_348_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_318_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_318_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
}
}
v___jp_279_:
{
size_t v___x_281_; size_t v___x_282_; 
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_add(v_i_268_, v___x_281_);
v_i_268_ = v___x_282_;
v_b_269_ = v_a_280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1___boxed(lean_object* v___x_358_, lean_object* v_as_359_, lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
size_t v_sz_boxed_372_; size_t v_i_boxed_373_; lean_object* v_res_374_; 
v_sz_boxed_372_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_373_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(v___x_358_, v_as_359_, v_sz_boxed_372_, v_i_boxed_373_, v_b_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_as_359_);
lean_dec_ref(v___x_358_);
return v_res_374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__3));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(lean_object* v_args_x3f_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
if (lean_obj_tag(v_args_x3f_390_) == 1)
{
lean_object* v_val_400_; lean_object* v_lctx_401_; lean_object* v___x_402_; lean_object* v___x_403_; size_t v_sz_404_; size_t v___x_405_; lean_object* v___x_406_; 
v_val_400_ = lean_ctor_get(v_args_x3f_390_, 0);
v_lctx_401_ = lean_ctor_get(v_a_395_, 2);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__2));
v_sz_404_ = lean_array_size(v_val_400_);
v___x_405_ = ((size_t)0ULL);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__1(v_lctx_401_, v_val_400_, v_sz_404_, v___x_405_, v___x_403_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_434_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_434_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_434_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_434_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_snd_411_; lean_object* v_fst_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_snd_411_ = lean_ctor_get(v_a_407_, 1);
lean_inc(v_snd_411_);
v_fst_412_ = lean_ctor_get(v_a_407_, 0);
lean_inc(v_fst_412_);
lean_dec(v_a_407_);
v_fst_413_ = lean_ctor_get(v_snd_411_, 0);
lean_inc(v_fst_413_);
v_snd_414_ = lean_ctor_get(v_snd_411_, 1);
lean_inc(v_snd_414_);
lean_dec(v_snd_411_);
v___x_421_ = lean_array_get_size(v_fst_412_);
v___x_422_ = lean_nat_dec_eq(v___x_421_, v___x_402_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
v___x_423_ = lean_unbox(v_fst_413_);
if (v___x_423_ == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_snd_414_);
lean_dec(v_fst_413_);
lean_dec(v_fst_412_);
lean_del_object(v___x_409_);
v___x_424_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__4);
v___x_425_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(v___x_424_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
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
else
{
goto v___jp_415_;
}
v___jp_415_:
{
lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_416_, 0, v_fst_412_);
lean_ctor_set(v___x_416_, 1, v_snd_414_);
v___x_417_ = lean_unbox(v_fst_413_);
lean_dec(v_fst_413_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*2, v___x_417_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_416_);
v___x_419_ = v___x_409_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_416_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_a_435_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_406_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_406_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___closed__5));
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs___boxed(lean_object* v_args_x3f_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v_args_x3f_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_args_x3f_445_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2(lean_object* v_00_u03b1_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(v_msg_457_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___boxed(lean_object* v_00_u03b1_468_, lean_object* v_msg_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2(v_00_u03b1_468_, v_msg_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0(lean_object* v_post_480_, lean_object* v_a_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc(v___y_489_);
lean_inc_ref(v___y_488_);
lean_inc(v___y_487_);
lean_inc_ref(v___y_486_);
lean_inc(v___y_485_);
lean_inc_ref(v___y_484_);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
v___x_493_ = lean_apply_11(v_post_480_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, lean_box(0));
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
if (lean_obj_tag(v_a_494_) == 0)
{
uint8_t v_done_495_; 
v_done_495_ = lean_ctor_get_uint8(v_a_494_, 0);
lean_dec_ref_known(v_a_494_, 0);
if (v_done_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_496_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_a_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v___x_496_;
}
else
{
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v___x_493_;
}
}
else
{
uint8_t v_done_497_; 
lean_dec_ref(v___y_482_);
v_done_497_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*1);
if (v_done_497_ == 0)
{
lean_object* v_e_x27_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref_known(v___x_493_, 1);
v_e_x27_498_ = lean_ctor_get(v_a_494_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_516_ == 0)
{
v___x_500_ = v_a_494_;
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_e_x27_498_);
lean_dec(v_a_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; 
lean_inc_ref(v_e_x27_498_);
v___x_502_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_a_481_, v_e_x27_498_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
if (lean_obj_tag(v_a_503_) == 0)
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_514_; 
lean_inc_ref(v_a_503_);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_502_, 0);
lean_dec(v_unused_515_);
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
else
{
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v_done_507_; lean_object* v___x_509_; 
v_done_507_ = lean_ctor_get_uint8(v_a_503_, 0);
lean_dec_ref_known(v_a_503_, 0);
if (v_isShared_501_ == 0)
{
v___x_509_ = v___x_500_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_e_x27_498_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*1, v_done_507_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_del_object(v___x_500_);
lean_dec_ref(v_e_x27_498_);
return v___x_502_;
}
}
else
{
lean_del_object(v___x_500_);
lean_dec_ref(v_e_x27_498_);
return v___x_502_;
}
}
}
else
{
lean_dec_ref_known(v_a_494_, 1);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v___x_493_;
}
}
}
else
{
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0___boxed(lean_object* v_post_517_, lean_object* v_a_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0(v_post_517_, v_a_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec_ref(v_a_518_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1(lean_object* v_fvarIds_531_, lean_object* v_x_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = l_Lean_FVarIdSet_ofArray(v_fvarIds_531_);
v___x_545_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v___x_544_, v___y_533_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1___boxed(lean_object* v_fvarIds_546_, lean_object* v_x_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1(v_fvarIds_546_, v_x_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v_fvarIds_546_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2(lean_object* v_pre_560_, lean_object* v___f_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(0);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
v___x_574_ = lean_apply_11(v_pre_560_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
if (lean_obj_tag(v_a_575_) == 0)
{
uint8_t v_done_576_; 
v_done_576_ = lean_ctor_get_uint8(v_a_575_, 0);
lean_dec_ref_known(v_a_575_, 0);
if (v_done_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec_ref_known(v___x_574_, 1);
v___x_577_ = lean_apply_12(v___f_561_, v___x_573_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
return v___x_577_;
}
else
{
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___f_561_);
return v___x_574_;
}
}
else
{
uint8_t v_done_578_; 
lean_dec_ref(v___y_562_);
v_done_578_ = lean_ctor_get_uint8(v_a_575_, sizeof(void*)*1);
if (v_done_578_ == 0)
{
lean_object* v_e_x27_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref_known(v___x_574_, 1);
v_e_x27_579_ = lean_ctor_get(v_a_575_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_575_);
if (v_isSharedCheck_597_ == 0)
{
v___x_581_ = v_a_575_;
v_isShared_582_ = v_isSharedCheck_597_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_e_x27_579_);
lean_dec(v_a_575_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_597_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
lean_inc_ref(v_e_x27_579_);
v___x_583_ = lean_apply_12(v___f_561_, v___x_573_, v_e_x27_579_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
if (lean_obj_tag(v_a_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_595_; 
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_596_);
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_595_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint8_t v_done_588_; lean_object* v___x_590_; 
v_done_588_ = lean_ctor_get_uint8(v_a_584_, 0);
lean_dec_ref_known(v_a_584_, 0);
if (v_isShared_582_ == 0)
{
v___x_590_ = v___x_581_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_e_x27_579_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*1, v_done_588_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_590_);
v___x_592_ = v___x_586_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_584_, 1);
lean_del_object(v___x_581_);
lean_dec_ref(v_e_x27_579_);
return v___x_583_;
}
}
else
{
lean_del_object(v___x_581_);
lean_dec_ref(v_e_x27_579_);
return v___x_583_;
}
}
}
else
{
lean_dec_ref_known(v_a_575_, 1);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___f_561_);
return v___x_574_;
}
}
}
else
{
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___f_561_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2___boxed(lean_object* v_pre_598_, lean_object* v___f_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2(v_pre_598_, v___f_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3(lean_object* v_pre_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; 
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc_ref(v___y_613_);
v___x_624_ = lean_apply_11(v_pre_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, lean_box(0));
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
if (lean_obj_tag(v_a_625_) == 0)
{
uint8_t v_done_626_; 
v_done_626_ = lean_ctor_get_uint8(v_a_625_, 0);
lean_dec_ref_known(v_a_625_, 0);
if (v_done_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref_known(v___x_624_, 1);
v___x_627_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_613_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v___x_627_;
}
else
{
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v___y_613_);
return v___x_624_;
}
}
else
{
uint8_t v_done_628_; 
lean_dec_ref(v___y_613_);
v_done_628_ = lean_ctor_get_uint8(v_a_625_, sizeof(void*)*1);
if (v_done_628_ == 0)
{
lean_object* v_e_x27_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref_known(v___x_624_, 1);
v_e_x27_629_ = lean_ctor_get(v_a_625_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_a_625_);
if (v_isSharedCheck_647_ == 0)
{
v___x_631_ = v_a_625_;
v_isShared_632_ = v_isSharedCheck_647_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_e_x27_629_);
lean_dec(v_a_625_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_647_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; 
lean_inc_ref(v_e_x27_629_);
v___x_633_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_629_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
if (lean_obj_tag(v_a_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
lean_inc_ref(v_a_634_);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_646_);
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v_done_638_; lean_object* v___x_640_; 
v_done_638_ = lean_ctor_get_uint8(v_a_634_, 0);
lean_dec_ref_known(v_a_634_, 0);
if (v_isShared_632_ == 0)
{
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_e_x27_629_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
lean_ctor_set_uint8(v___x_640_, sizeof(void*)*1, v_done_638_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_640_);
v___x_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_del_object(v___x_631_);
lean_dec_ref(v_e_x27_629_);
return v___x_633_;
}
}
else
{
lean_del_object(v___x_631_);
lean_dec_ref(v_e_x27_629_);
return v___x_633_;
}
}
}
else
{
lean_dec_ref_known(v_a_625_, 1);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v___x_624_;
}
}
}
else
{
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v___y_613_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3___boxed(lean_object* v_pre_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3(v_pre_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(lean_object* v_methods_661_, lean_object* v_args_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___y_669_; lean_object* v_post_670_; lean_object* v_pre_673_; lean_object* v_post_674_; lean_object* v_fvarIds_675_; uint8_t v_zetaDeltaAll_676_; lean_object* v_declNames_677_; lean_object* v_pre_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v_pre_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; 
v_pre_673_ = lean_ctor_get(v_methods_661_, 0);
lean_inc_ref(v_pre_673_);
v_post_674_ = lean_ctor_get(v_methods_661_, 1);
lean_inc_ref(v_post_674_);
lean_dec_ref(v_methods_661_);
v_fvarIds_675_ = lean_ctor_get(v_args_662_, 0);
lean_inc_ref(v_fvarIds_675_);
v_zetaDeltaAll_676_ = lean_ctor_get_uint8(v_args_662_, sizeof(void*)*2);
v_declNames_677_ = lean_ctor_get(v_args_662_, 1);
lean_inc_ref(v_declNames_677_);
lean_dec_ref(v_args_662_);
if (v_zetaDeltaAll_676_ == 0)
{
v_pre_699_ = v_pre_673_;
v___y_700_ = v_a_663_;
v___y_701_ = v_a_664_;
v___y_702_ = v_a_665_;
v___y_703_ = v_a_666_;
goto v___jp_698_;
}
else
{
lean_object* v_pre_709_; 
v_pre_709_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_709_, 0, v_pre_673_);
v_pre_699_ = v_pre_709_;
v___y_700_ = v_a_663_;
v___y_701_ = v_a_664_;
v___y_702_ = v_a_665_;
v___y_703_ = v_a_666_;
goto v___jp_698_;
}
v___jp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___y_669_);
lean_ctor_set(v___x_671_, 1, v_post_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
v___jp_678_:
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_684_ = lean_array_get_size(v_declNames_677_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_nat_dec_eq(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Sym_DSimp_Decls_ofNames(v_declNames_677_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec_ref(v_declNames_677_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___f_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___f_689_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__0___boxed), 13, 2);
lean_closure_set(v___f_689_, 0, v_post_674_);
lean_closure_set(v___f_689_, 1, v_a_688_);
v___y_669_ = v_pre_679_;
v_post_670_ = v___f_689_;
goto v___jp_668_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v_pre_679_);
lean_dec_ref(v_post_674_);
v_a_690_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_687_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_687_);
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
else
{
lean_dec_ref(v_declNames_677_);
v___y_669_ = v_pre_679_;
v_post_670_ = v_post_674_;
goto v___jp_668_;
}
}
v___jp_698_:
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_array_get_size(v_fvarIds_675_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_nat_dec_eq(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___f_707_; lean_object* v_pre_708_; 
v___f_707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_707_, 0, v_fvarIds_675_);
v_pre_708_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___lam__2___boxed), 13, 2);
lean_closure_set(v_pre_708_, 0, v_pre_699_);
lean_closure_set(v_pre_708_, 1, v___f_707_);
v_pre_679_ = v_pre_708_;
v___y_680_ = v___y_700_;
v___y_681_ = v___y_701_;
v___y_682_ = v___y_702_;
v___y_683_ = v___y_703_;
goto v___jp_678_;
}
else
{
lean_dec_ref(v_fvarIds_675_);
v_pre_679_ = v_pre_699_;
v___y_680_ = v___y_700_;
v___y_681_ = v___y_701_;
v___y_682_ = v___y_702_;
v___y_683_ = v___y_703_;
goto v___jp_678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg___boxed(lean_object* v_methods_710_, lean_object* v_args_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v_methods_710_, v_args_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(lean_object* v_methods_718_, lean_object* v_args_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v_methods_718_, v_args_719_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___boxed(lean_object* v_methods_730_, lean_object* v_args_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs(v_methods_730_, v_args_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(lean_object* v_x_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
lean_inc_ref(v___y_743_);
v___x_754_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_743_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
if (lean_obj_tag(v_a_755_) == 0)
{
uint8_t v_done_756_; 
v_done_756_ = lean_ctor_get_uint8(v_a_755_, 0);
lean_dec_ref_known(v_a_755_, 0);
if (v_done_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref_known(v___x_754_, 1);
v___x_757_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_743_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v___y_743_);
return v___x_757_;
}
else
{
lean_dec_ref(v___y_743_);
return v___x_754_;
}
}
else
{
uint8_t v_done_758_; 
lean_dec_ref(v___y_743_);
v_done_758_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*1);
if (v_done_758_ == 0)
{
lean_object* v_e_x27_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref_known(v___x_754_, 1);
v_e_x27_759_ = lean_ctor_get(v_a_755_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_777_ == 0)
{
v___x_761_ = v_a_755_;
v_isShared_762_ = v_isSharedCheck_777_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_e_x27_759_);
lean_dec(v_a_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_777_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_759_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
if (lean_obj_tag(v_a_764_) == 0)
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_775_; 
lean_inc_ref(v_a_764_);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_763_, 0);
lean_dec(v_unused_776_);
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
else
{
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
uint8_t v_done_768_; lean_object* v___x_770_; 
v_done_768_ = lean_ctor_get_uint8(v_a_764_, 0);
lean_dec_ref_known(v_a_764_, 0);
if (v_isShared_762_ == 0)
{
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_e_x27_759_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*1, v_done_768_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_770_);
v___x_772_ = v___x_766_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
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
else
{
lean_del_object(v___x_761_);
lean_dec_ref(v_e_x27_759_);
return v___x_763_;
}
}
else
{
lean_del_object(v___x_761_);
lean_dec_ref(v_e_x27_759_);
return v___x_763_;
}
}
}
else
{
lean_dec_ref_known(v_a_755_, 1);
return v___x_754_;
}
}
}
else
{
lean_dec_ref(v___y_743_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0___boxed(lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__0(v_x_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(lean_object* v___f_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
lean_inc_ref(v___y_792_);
v___x_804_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_792_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
if (lean_obj_tag(v_a_805_) == 0)
{
uint8_t v_done_806_; 
v_done_806_ = lean_ctor_get_uint8(v_a_805_, 0);
lean_dec_ref_known(v_a_805_, 0);
if (v_done_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref_known(v___x_804_, 1);
v___x_807_ = lean_apply_12(v___f_791_, v___x_803_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, lean_box(0));
return v___x_807_;
}
else
{
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v___f_791_);
return v___x_804_;
}
}
else
{
uint8_t v_done_808_; 
lean_dec_ref(v___y_792_);
v_done_808_ = lean_ctor_get_uint8(v_a_805_, sizeof(void*)*1);
if (v_done_808_ == 0)
{
lean_object* v_e_x27_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref_known(v___x_804_, 1);
v_e_x27_809_ = lean_ctor_get(v_a_805_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_827_ == 0)
{
v___x_811_ = v_a_805_;
v_isShared_812_ = v_isSharedCheck_827_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_e_x27_809_);
lean_dec(v_a_805_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_827_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; 
lean_inc_ref(v_e_x27_809_);
v___x_813_ = lean_apply_12(v___f_791_, v___x_803_, v_e_x27_809_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, lean_box(0));
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
if (lean_obj_tag(v_a_814_) == 0)
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_825_; 
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_813_, 0);
lean_dec(v_unused_826_);
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_825_;
goto v_resetjp_815_;
}
else
{
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_825_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v_done_818_; lean_object* v___x_820_; 
v_done_818_ = lean_ctor_get_uint8(v_a_814_, 0);
lean_dec_ref_known(v_a_814_, 0);
if (v_isShared_812_ == 0)
{
v___x_820_ = v___x_811_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_e_x27_809_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_822_; 
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*1, v_done_818_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_814_, 1);
lean_del_object(v___x_811_);
lean_dec_ref(v_e_x27_809_);
return v___x_813_;
}
}
else
{
lean_del_object(v___x_811_);
lean_dec_ref(v_e_x27_809_);
return v___x_813_;
}
}
}
else
{
lean_dec_ref_known(v_a_805_, 1);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___f_791_);
return v___x_804_;
}
}
}
else
{
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v___f_791_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1___boxed(lean_object* v___f_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___lam__1(v___f_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(lean_object* v_args_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___closed__4));
v___x_859_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v___x_858_, v_args_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg___boxed(lean_object* v_args_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(lean_object* v_args_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_867_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___boxed(lean_object* v_args_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods(v_args_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg(){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___closed__0));
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg___boxed(lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(lean_object* v_x_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___redArg();
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed(lean_object* v_x_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc(v_x_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_x_908_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(lean_object* v_stx_x3f_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
if (lean_obj_tag(v_stx_x3f_920_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_931_; 
v_val_930_ = lean_ctor_get(v_stx_x3f_920_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v_stx_x3f_920_, 1);
v___x_931_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(v_val_930_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v_stx_x3f_920_);
v___x_932_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_trivialDSimproc___boxed), 11, 0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc___boxed(lean_object* v_stx_x3f_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_stx_x3f_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_944_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__0));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__2));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(lean_object* v_variantName_954_, lean_object* v_args_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_Name_isAnonymous(v_variantName_954_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v_env_967_; lean_object* v___x_968_; 
v___x_966_ = lean_st_ref_get(v_a_963_);
v_env_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc_ref(v_env_967_);
lean_dec(v___x_966_);
v___x_968_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_967_, v_variantName_954_);
if (lean_obj_tag(v___x_968_) == 1)
{
lean_object* v_val_969_; lean_object* v_pre_x3f_970_; lean_object* v_post_x3f_971_; lean_object* v_config_972_; lean_object* v___x_973_; 
lean_dec(v_variantName_954_);
v_val_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v___x_968_, 1);
v_pre_x3f_970_ = lean_ctor_get(v_val_969_, 0);
lean_inc(v_pre_x3f_970_);
v_post_x3f_971_ = lean_ctor_get(v_val_969_, 1);
lean_inc(v_post_x3f_971_);
v_config_972_ = lean_ctor_get(v_val_969_, 2);
lean_inc_ref(v_config_972_);
lean_dec(v_val_969_);
v___x_973_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_pre_x3f_970_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabOptDSimproc(v_post_x3f_971_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_a_974_);
lean_ctor_set(v___x_977_, 1, v_a_976_);
v___x_978_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_addDSimpArgs___redArg(v___x_977_, v_args_955_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v_a_979_);
lean_ctor_set(v___x_983_, 1, v_config_972_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_config_972_);
v_a_988_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_978_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_978_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_974_);
lean_dec_ref(v_config_972_);
lean_dec_ref(v_args_955_);
v_a_996_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_975_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_975_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_config_972_);
lean_dec(v_post_x3f_971_);
lean_dec_ref(v_args_955_);
v_a_1004_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_973_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_973_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_968_);
lean_dec_ref(v_args_955_);
v___x_1012_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__1);
v___x_1013_ = l_Lean_MessageData_ofName(v_variantName_954_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__3);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(v___x_1016_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_1017_;
}
}
else
{
lean_object* v___x_1018_; 
lean_dec(v_variantName_954_);
v___x_1018_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_mkDSimpDefaultMethods___redArg(v_args_955_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1028_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___closed__4));
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_a_1019_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1024_);
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1018_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1018_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant___boxed(lean_object* v_variantName_1037_, lean_object* v_args_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v_variantName_1037_, v_args_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1048_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg(){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___closed__0);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg___boxed(lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(lean_object* v_00_u03b1_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___boxed(lean_object* v_00_u03b1_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0(v_00_u03b1_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
v___x_1090_ = lean_apply_10(v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, lean_box(0));
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed(lean_object* v_x_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0(v_x_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(lean_object* v_mvarId_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___f_1115_; lean_object* v___x_1116_; 
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1105_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1115_, 0, v_x_1104_);
lean_closure_set(v___f_1115_, 1, v___y_1105_);
lean_closure_set(v___f_1115_, 2, v___y_1106_);
lean_closure_set(v___f_1115_, 3, v___y_1107_);
lean_closure_set(v___f_1115_, 4, v___y_1108_);
lean_closure_set(v___f_1115_, 5, v___y_1109_);
v___x_1116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1103_, v___f_1115_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1116_) == 0)
{
return v___x_1116_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg___boxed(lean_object* v_mvarId_1125_, lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_1125_, v_x_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(lean_object* v_00_u03b1_1138_, lean_object* v_mvarId_1139_, lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___redArg(v_mvarId_1139_, v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_mvarId_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1(v_00_u03b1_1152_, v_mvarId_1153_, v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(lean_object* v_mvarId_1166_, lean_object* v_fst_1167_, lean_object* v_snd_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_MVarId_getType(v_mvarId_1166_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_1182_, 0, v_a_1181_);
v___x_1183_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_1182_, v_fst_1167_, v_snd_1168_, v___y_1169_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1183_;
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_snd_1168_);
lean_dec_ref(v_fst_1167_);
v_a_1184_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1180_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1180_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed(lean_object* v_mvarId_1192_, lean_object* v_fst_1193_, lean_object* v_snd_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0(v_mvarId_1192_, v_fst_1193_, v_snd_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_ks_1211_; lean_object* v_vs_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1236_; 
v_ks_1211_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1212_ = lean_ctor_get(v_x_1207_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1214_ = v_x_1207_;
v_isShared_1215_ = v_isSharedCheck_1236_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_vs_1212_);
lean_inc(v_ks_1211_);
lean_dec(v_x_1207_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1236_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_array_get_size(v_ks_1211_);
v___x_1217_ = lean_nat_dec_lt(v_x_1208_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
lean_dec(v_x_1208_);
v___x_1218_ = lean_array_push(v_ks_1211_, v_x_1209_);
v___x_1219_ = lean_array_push(v_vs_1212_, v_x_1210_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1219_);
lean_ctor_set(v___x_1214_, 0, v___x_1218_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
else
{
lean_object* v_k_x27_1223_; uint8_t v___x_1224_; 
v_k_x27_1223_ = lean_array_fget_borrowed(v_ks_1211_, v_x_1208_);
v___x_1224_ = l_Lean_instBEqMVarId_beq(v_x_1209_, v_k_x27_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1226_; 
if (v_isShared_1215_ == 0)
{
v___x_1226_ = v___x_1214_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_ks_1211_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_vs_1212_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_x_1208_, v___x_1227_);
lean_dec(v_x_1208_);
v_x_1207_ = v___x_1226_;
v_x_1208_ = v___x_1228_;
goto _start;
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1231_ = lean_array_fset(v_ks_1211_, v_x_1208_, v_x_1209_);
v___x_1232_ = lean_array_fset(v_vs_1212_, v_x_1208_, v_x_1210_);
lean_dec(v_x_1208_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1232_);
lean_ctor_set(v___x_1214_, 0, v___x_1231_);
v___x_1234_ = v___x_1214_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(lean_object* v_n_1237_, lean_object* v_k_1238_, lean_object* v_v_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_n_1237_, v___x_1240_, v_k_1238_, v_v_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1243_, size_t v_x_1244_, size_t v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
lean_object* v_es_1248_; size_t v___x_1249_; size_t v___x_1250_; lean_object* v_j_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_es_1248_ = lean_ctor_get(v_x_1243_, 0);
v___x_1249_ = ((size_t)31ULL);
v___x_1250_ = lean_usize_land(v_x_1244_, v___x_1249_);
v_j_1251_ = lean_usize_to_nat(v___x_1250_);
v___x_1252_ = lean_array_get_size(v_es_1248_);
v___x_1253_ = lean_nat_dec_lt(v_j_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v_j_1251_);
lean_dec(v_x_1247_);
lean_dec(v_x_1246_);
return v_x_1243_;
}
else
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1292_; 
lean_inc_ref(v_es_1248_);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_x_1243_, 0);
lean_dec(v_unused_1293_);
v___x_1255_ = v_x_1243_;
v_isShared_1256_ = v_isSharedCheck_1292_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v_x_1243_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1292_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_v_1257_; lean_object* v___x_1258_; lean_object* v_xs_x27_1259_; lean_object* v___y_1261_; 
v_v_1257_ = lean_array_fget(v_es_1248_, v_j_1251_);
v___x_1258_ = lean_box(0);
v_xs_x27_1259_ = lean_array_fset(v_es_1248_, v_j_1251_, v___x_1258_);
switch(lean_obj_tag(v_v_1257_))
{
case 0:
{
lean_object* v_key_1266_; lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1277_; 
v_key_1266_ = lean_ctor_get(v_v_1257_, 0);
v_val_1267_ = lean_ctor_get(v_v_1257_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_v_1257_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1269_ = v_v_1257_;
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_inc(v_key_1266_);
lean_dec(v_v_1257_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
uint8_t v___x_1271_; 
v___x_1271_ = l_Lean_instBEqMVarId_beq(v_x_1246_, v_key_1266_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_del_object(v___x_1269_);
v___x_1272_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1266_, v_val_1267_, v_x_1246_, v_x_1247_);
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
v___y_1261_ = v___x_1273_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_val_1267_);
lean_dec(v_key_1266_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_x_1247_);
lean_ctor_set(v___x_1269_, 0, v_x_1246_);
v___x_1275_ = v___x_1269_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_x_1246_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_x_1247_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
v___y_1261_ = v___x_1275_;
goto v___jp_1260_;
}
}
}
}
case 1:
{
lean_object* v_node_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1290_; 
v_node_1278_ = lean_ctor_get(v_v_1257_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_v_1257_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1280_ = v_v_1257_;
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_node_1278_);
lean_dec(v_v_1257_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
size_t v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1282_ = ((size_t)5ULL);
v___x_1283_ = lean_usize_shift_right(v_x_1244_, v___x_1282_);
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = lean_usize_add(v_x_1245_, v___x_1284_);
v___x_1286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_node_1278_, v___x_1283_, v___x_1285_, v_x_1246_, v_x_1247_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1286_);
v___x_1288_ = v___x_1280_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v___y_1261_ = v___x_1288_;
goto v___jp_1260_;
}
}
}
default: 
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_x_1246_);
lean_ctor_set(v___x_1291_, 1, v_x_1247_);
v___y_1261_ = v___x_1291_;
goto v___jp_1260_;
}
}
v___jp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_array_fset(v_xs_x27_1259_, v_j_1251_, v___y_1261_);
lean_dec(v_j_1251_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1262_);
v___x_1264_ = v___x_1255_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
else
{
lean_object* v_ks_1294_; lean_object* v_vs_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1313_; 
v_ks_1294_ = lean_ctor_get(v_x_1243_, 0);
v_vs_1295_ = lean_ctor_get(v_x_1243_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1297_ = v_x_1243_;
v_isShared_1298_ = v_isSharedCheck_1313_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_vs_1295_);
lean_inc(v_ks_1294_);
lean_dec(v_x_1243_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1313_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_ks_1294_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_vs_1295_);
v___x_1300_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v_newNode_1301_; size_t v___x_1302_; uint8_t v___x_1303_; 
v_newNode_1301_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v___x_1300_, v_x_1246_, v_x_1247_);
v___x_1302_ = ((size_t)7ULL);
v___x_1303_ = lean_usize_dec_le(v___x_1302_, v_x_1245_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1301_);
v___x_1305_ = lean_unsigned_to_nat(4u);
v___x_1306_ = lean_nat_dec_lt(v___x_1304_, v___x_1305_);
lean_dec(v___x_1304_);
if (v___x_1306_ == 0)
{
lean_object* v_ks_1307_; lean_object* v_vs_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_ks_1307_ = lean_ctor_get(v_newNode_1301_, 0);
lean_inc_ref(v_ks_1307_);
v_vs_1308_ = lean_ctor_get(v_newNode_1301_, 1);
lean_inc_ref(v_vs_1308_);
lean_dec_ref(v_newNode_1301_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___closed__0);
v___x_1311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_x_1245_, v_ks_1307_, v_vs_1308_, v___x_1309_, v___x_1310_);
lean_dec_ref(v_vs_1308_);
lean_dec_ref(v_ks_1307_);
return v___x_1311_;
}
else
{
return v_newNode_1301_;
}
}
else
{
return v_newNode_1301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(size_t v_depth_1314_, lean_object* v_keys_1315_, lean_object* v_vals_1316_, lean_object* v_i_1317_, lean_object* v_entries_1318_){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = lean_array_get_size(v_keys_1315_);
v___x_1320_ = lean_nat_dec_lt(v_i_1317_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_dec(v_i_1317_);
return v_entries_1318_;
}
else
{
lean_object* v_k_1321_; lean_object* v_v_1322_; uint64_t v___x_1323_; size_t v_h_1324_; size_t v___x_1325_; lean_object* v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v_h_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_k_1321_ = lean_array_fget_borrowed(v_keys_1315_, v_i_1317_);
v_v_1322_ = lean_array_fget_borrowed(v_vals_1316_, v_i_1317_);
v___x_1323_ = l_Lean_instHashableMVarId_hash(v_k_1321_);
v_h_1324_ = lean_uint64_to_usize(v___x_1323_);
v___x_1325_ = ((size_t)5ULL);
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_sub(v_depth_1314_, v___x_1327_);
v___x_1329_ = lean_usize_mul(v___x_1325_, v___x_1328_);
v_h_1330_ = lean_usize_shift_right(v_h_1324_, v___x_1329_);
v___x_1331_ = lean_nat_add(v_i_1317_, v___x_1326_);
lean_dec(v_i_1317_);
lean_inc(v_v_1322_);
lean_inc(v_k_1321_);
v___x_1332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_entries_1318_, v_h_1330_, v_depth_1314_, v_k_1321_, v_v_1322_);
v_i_1317_ = v___x_1331_;
v_entries_1318_ = v___x_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_1334_, lean_object* v_keys_1335_, lean_object* v_vals_1336_, lean_object* v_i_1337_, lean_object* v_entries_1338_){
_start:
{
size_t v_depth_boxed_1339_; lean_object* v_res_1340_; 
v_depth_boxed_1339_ = lean_unbox_usize(v_depth_1334_);
lean_dec(v_depth_1334_);
v_res_1340_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_boxed_1339_, v_keys_1335_, v_vals_1336_, v_i_1337_, v_entries_1338_);
lean_dec_ref(v_vals_1336_);
lean_dec_ref(v_keys_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
size_t v_x_8768__boxed_1346_; size_t v_x_8769__boxed_1347_; lean_object* v_res_1348_; 
v_x_8768__boxed_1346_ = lean_unbox_usize(v_x_1342_);
lean_dec(v_x_1342_);
v_x_8769__boxed_1347_ = lean_unbox_usize(v_x_1343_);
lean_dec(v_x_1343_);
v_res_1348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1341_, v_x_8768__boxed_1346_, v_x_8769__boxed_1347_, v_x_1344_, v_x_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
uint64_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = l_Lean_instHashableMVarId_hash(v_x_1350_);
v___x_1353_ = lean_uint64_to_usize(v___x_1352_);
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1349_, v___x_1353_, v___x_1354_, v_x_1350_, v_x_1351_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(lean_object* v_mvarId_1356_, lean_object* v_val_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v_mctx_1361_; lean_object* v_cache_1362_; lean_object* v_zetaDeltaFVarIds_1363_; lean_object* v_postponed_1364_; lean_object* v_diag_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1394_; 
v___x_1360_ = lean_st_ref_take(v___y_1358_);
v_mctx_1361_ = lean_ctor_get(v___x_1360_, 0);
v_cache_1362_ = lean_ctor_get(v___x_1360_, 1);
v_zetaDeltaFVarIds_1363_ = lean_ctor_get(v___x_1360_, 2);
v_postponed_1364_ = lean_ctor_get(v___x_1360_, 3);
v_diag_1365_ = lean_ctor_get(v___x_1360_, 4);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1367_ = v___x_1360_;
v_isShared_1368_ = v_isSharedCheck_1394_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_diag_1365_);
lean_inc(v_postponed_1364_);
lean_inc(v_zetaDeltaFVarIds_1363_);
lean_inc(v_cache_1362_);
lean_inc(v_mctx_1361_);
lean_dec(v___x_1360_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1394_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_depth_1369_; lean_object* v_levelAssignDepth_1370_; lean_object* v_lmvarCounter_1371_; lean_object* v_mvarCounter_1372_; lean_object* v_lDecls_1373_; lean_object* v_decls_1374_; lean_object* v_userNames_1375_; lean_object* v_lAssignment_1376_; lean_object* v_eAssignment_1377_; lean_object* v_dAssignment_1378_; lean_object* v_instanceTypedMVars_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1393_; 
v_depth_1369_ = lean_ctor_get(v_mctx_1361_, 0);
v_levelAssignDepth_1370_ = lean_ctor_get(v_mctx_1361_, 1);
v_lmvarCounter_1371_ = lean_ctor_get(v_mctx_1361_, 2);
v_mvarCounter_1372_ = lean_ctor_get(v_mctx_1361_, 3);
v_lDecls_1373_ = lean_ctor_get(v_mctx_1361_, 4);
v_decls_1374_ = lean_ctor_get(v_mctx_1361_, 5);
v_userNames_1375_ = lean_ctor_get(v_mctx_1361_, 6);
v_lAssignment_1376_ = lean_ctor_get(v_mctx_1361_, 7);
v_eAssignment_1377_ = lean_ctor_get(v_mctx_1361_, 8);
v_dAssignment_1378_ = lean_ctor_get(v_mctx_1361_, 9);
v_instanceTypedMVars_1379_ = lean_ctor_get(v_mctx_1361_, 10);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_mctx_1361_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1381_ = v_mctx_1361_;
v_isShared_1382_ = v_isSharedCheck_1393_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_instanceTypedMVars_1379_);
lean_inc(v_dAssignment_1378_);
lean_inc(v_eAssignment_1377_);
lean_inc(v_lAssignment_1376_);
lean_inc(v_userNames_1375_);
lean_inc(v_decls_1374_);
lean_inc(v_lDecls_1373_);
lean_inc(v_mvarCounter_1372_);
lean_inc(v_lmvarCounter_1371_);
lean_inc(v_levelAssignDepth_1370_);
lean_inc(v_depth_1369_);
lean_dec(v_mctx_1361_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1393_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_eAssignment_1377_, v_mvarId_1356_, v_val_1357_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 8, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_depth_1369_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_levelAssignDepth_1370_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_lmvarCounter_1371_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_mvarCounter_1372_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_lDecls_1373_);
lean_ctor_set(v_reuseFailAlloc_1392_, 5, v_decls_1374_);
lean_ctor_set(v_reuseFailAlloc_1392_, 6, v_userNames_1375_);
lean_ctor_set(v_reuseFailAlloc_1392_, 7, v_lAssignment_1376_);
lean_ctor_set(v_reuseFailAlloc_1392_, 8, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1392_, 9, v_dAssignment_1378_);
lean_ctor_set(v_reuseFailAlloc_1392_, 10, v_instanceTypedMVars_1379_);
v___x_1386_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1386_);
v___x_1388_ = v___x_1367_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_cache_1362_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_zetaDeltaFVarIds_1363_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_postponed_1364_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_diag_1365_);
v___x_1388_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_st_ref_put(v___y_1358_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1383_);
return v___x_1390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg___boxed(lean_object* v_mvarId_1395_, lean_object* v_val_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1395_, v_val_1396_, v___y_1397_);
lean_dec(v___y_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(lean_object* v_a_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
uint8_t v___x_1402_; 
v___x_1402_ = 0;
return v___x_1402_;
}
else
{
lean_object* v_key_1403_; lean_object* v_tail_1404_; uint8_t v___x_1405_; 
v_key_1403_ = lean_ctor_get(v_x_1401_, 0);
v_tail_1404_ = lean_ctor_get(v_x_1401_, 2);
v___x_1405_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1403_, v_a_1400_);
if (v___x_1405_ == 0)
{
v_x_1401_ = v_tail_1404_;
goto _start;
}
else
{
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg___boxed(lean_object* v_a_1407_, lean_object* v_x_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1407_, v_x_1408_);
lean_dec(v_x_1408_);
lean_dec_ref(v_a_1407_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(lean_object* v_a_1411_, lean_object* v_b_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_dec(v_b_1412_);
lean_dec_ref(v_a_1411_);
return v_x_1413_;
}
else
{
lean_object* v_key_1414_; lean_object* v_value_1415_; lean_object* v_tail_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1428_; 
v_key_1414_ = lean_ctor_get(v_x_1413_, 0);
v_value_1415_ = lean_ctor_get(v_x_1413_, 1);
v_tail_1416_ = lean_ctor_get(v_x_1413_, 2);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1418_ = v_x_1413_;
v_isShared_1419_ = v_isSharedCheck_1428_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_tail_1416_);
lean_inc(v_value_1415_);
lean_inc(v_key_1414_);
lean_dec(v_x_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1428_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1414_, v_a_1411_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1411_, v_b_1412_, v_tail_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 2, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_key_1414_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_value_1415_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_value_1415_);
lean_dec(v_key_1414_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_b_1412_);
lean_ctor_set(v___x_1418_, 0, v_a_1411_);
v___x_1426_ = v___x_1418_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_b_1412_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_tail_1416_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
return v_x_1429_;
}
else
{
lean_object* v_key_1431_; lean_object* v_value_1432_; lean_object* v_tail_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1456_; 
v_key_1431_ = lean_ctor_get(v_x_1430_, 0);
v_value_1432_ = lean_ctor_get(v_x_1430_, 1);
v_tail_1433_ = lean_ctor_get(v_x_1430_, 2);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1430_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1435_ = v_x_1430_;
v_isShared_1436_ = v_isSharedCheck_1456_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_tail_1433_);
lean_inc(v_value_1432_);
lean_inc(v_key_1431_);
lean_dec(v_x_1430_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1456_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; uint64_t v___x_1440_; uint64_t v_fold_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; uint64_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1437_ = lean_array_get_size(v_x_1429_);
v___x_1438_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_key_1431_);
v___x_1439_ = 32ULL;
v___x_1440_ = lean_uint64_shift_right(v___x_1438_, v___x_1439_);
v_fold_1441_ = lean_uint64_xor(v___x_1438_, v___x_1440_);
v___x_1442_ = 16ULL;
v___x_1443_ = lean_uint64_shift_right(v_fold_1441_, v___x_1442_);
v___x_1444_ = lean_uint64_xor(v_fold_1441_, v___x_1443_);
v___x_1445_ = lean_uint64_to_usize(v___x_1444_);
v___x_1446_ = lean_usize_of_nat(v___x_1437_);
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_sub(v___x_1446_, v___x_1447_);
v___x_1449_ = lean_usize_land(v___x_1445_, v___x_1448_);
v___x_1450_ = lean_array_uget_borrowed(v_x_1429_, v___x_1449_);
lean_inc(v___x_1450_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 2, v___x_1450_);
v___x_1452_ = v___x_1435_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_key_1431_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_value_1432_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_array_uset(v_x_1429_, v___x_1449_, v___x_1452_);
v_x_1429_ = v___x_1453_;
v_x_1430_ = v_tail_1433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1457_, lean_object* v_source_1458_, lean_object* v_target_1459_){
_start:
{
lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_array_get_size(v_source_1458_);
v___x_1461_ = lean_nat_dec_lt(v_i_1457_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec_ref(v_source_1458_);
lean_dec(v_i_1457_);
return v_target_1459_;
}
else
{
lean_object* v_es_1462_; lean_object* v___x_1463_; lean_object* v_source_1464_; lean_object* v_target_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_es_1462_ = lean_array_fget(v_source_1458_, v_i_1457_);
v___x_1463_ = lean_box(0);
v_source_1464_ = lean_array_fset(v_source_1458_, v_i_1457_, v___x_1463_);
v_target_1465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1459_, v_es_1462_);
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_add(v_i_1457_, v___x_1466_);
lean_dec(v_i_1457_);
v_i_1457_ = v___x_1467_;
v_source_1458_ = v_source_1464_;
v_target_1459_ = v_target_1465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(lean_object* v_data_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_nbuckets_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1470_ = lean_array_get_size(v_data_1469_);
v___x_1471_ = lean_unsigned_to_nat(2u);
v_nbuckets_1472_ = lean_nat_mul(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_mk_array(v_nbuckets_1472_, v___x_1474_);
v___x_1476_ = lean_array_propagate_mark(v_data_1469_, v___x_1475_);
v___x_1477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v___x_1473_, v_data_1469_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(lean_object* v_m_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_){
_start:
{
lean_object* v_size_1481_; lean_object* v_buckets_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1525_; 
v_size_1481_ = lean_ctor_get(v_m_1478_, 0);
v_buckets_1482_ = lean_ctor_get(v_m_1478_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_m_1478_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1484_ = v_m_1478_;
v_isShared_1485_ = v_isSharedCheck_1525_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_buckets_1482_);
lean_inc(v_size_1481_);
lean_dec(v_m_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1525_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v___x_1489_; uint64_t v_fold_1490_; uint64_t v___x_1491_; uint64_t v___x_1492_; uint64_t v___x_1493_; size_t v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; lean_object* v_bkt_1499_; uint8_t v___x_1500_; 
v___x_1486_ = lean_array_get_size(v_buckets_1482_);
v___x_1487_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1479_);
v___x_1488_ = 32ULL;
v___x_1489_ = lean_uint64_shift_right(v___x_1487_, v___x_1488_);
v_fold_1490_ = lean_uint64_xor(v___x_1487_, v___x_1489_);
v___x_1491_ = 16ULL;
v___x_1492_ = lean_uint64_shift_right(v_fold_1490_, v___x_1491_);
v___x_1493_ = lean_uint64_xor(v_fold_1490_, v___x_1492_);
v___x_1494_ = lean_uint64_to_usize(v___x_1493_);
v___x_1495_ = lean_usize_of_nat(v___x_1486_);
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_sub(v___x_1495_, v___x_1496_);
v___x_1498_ = lean_usize_land(v___x_1494_, v___x_1497_);
v_bkt_1499_ = lean_array_uget_borrowed(v_buckets_1482_, v___x_1498_);
v___x_1500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1479_, v_bkt_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v_size_x27_1502_; lean_object* v___x_1503_; lean_object* v_buckets_x27_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1501_ = lean_unsigned_to_nat(1u);
v_size_x27_1502_ = lean_nat_add(v_size_1481_, v___x_1501_);
lean_dec(v_size_1481_);
lean_inc(v_bkt_1499_);
v___x_1503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1479_);
lean_ctor_set(v___x_1503_, 1, v_b_1480_);
lean_ctor_set(v___x_1503_, 2, v_bkt_1499_);
v_buckets_x27_1504_ = lean_array_uset(v_buckets_1482_, v___x_1498_, v___x_1503_);
v___x_1505_ = lean_unsigned_to_nat(4u);
v___x_1506_ = lean_nat_mul(v_size_x27_1502_, v___x_1505_);
v___x_1507_ = lean_unsigned_to_nat(3u);
v___x_1508_ = lean_nat_div(v___x_1506_, v___x_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_array_get_size(v_buckets_x27_1504_);
v___x_1510_ = lean_nat_dec_le(v___x_1508_, v___x_1509_);
lean_dec(v___x_1508_);
if (v___x_1510_ == 0)
{
lean_object* v_val_1511_; lean_object* v___x_1513_; 
v_val_1511_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_buckets_x27_1504_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_val_1511_);
lean_ctor_set(v___x_1484_, 0, v_size_x27_1502_);
v___x_1513_ = v___x_1484_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_size_x27_1502_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_val_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
else
{
lean_object* v___x_1516_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_buckets_x27_1504_);
lean_ctor_set(v___x_1484_, 0, v_size_x27_1502_);
v___x_1516_ = v___x_1484_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_size_x27_1502_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_buckets_x27_1504_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v_buckets_x27_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_inc(v_bkt_1499_);
v___x_1518_ = lean_box(0);
v_buckets_x27_1519_ = lean_array_uset(v_buckets_1482_, v___x_1498_, v___x_1518_);
v___x_1520_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1479_, v_b_1480_, v_bkt_1499_);
v___x_1521_ = lean_array_uset(v_buckets_x27_1519_, v___x_1498_, v___x_1520_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v___x_1521_);
v___x_1523_ = v___x_1484_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_size_1481_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(lean_object* v_a_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
else
{
lean_object* v_key_1529_; lean_object* v_value_1530_; lean_object* v_tail_1531_; uint8_t v___x_1532_; 
v_key_1529_ = lean_ctor_get(v_x_1527_, 0);
v_value_1530_ = lean_ctor_get(v_x_1527_, 1);
v_tail_1531_ = lean_ctor_get(v_x_1527_, 2);
v___x_1532_ = l_Lean_Elab_Tactic_Grind_instBEqDSimpCacheKey_beq(v_key_1529_, v_a_1526_);
if (v___x_1532_ == 0)
{
v_x_1527_ = v_tail_1531_;
goto _start;
}
else
{
lean_object* v___x_1534_; 
lean_inc(v_value_1530_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_value_1530_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg___boxed(lean_object* v_a_1535_, lean_object* v_x_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1535_, v_x_1536_);
lean_dec(v_x_1536_);
lean_dec_ref(v_a_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(lean_object* v_m_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_buckets_1540_; lean_object* v___x_1541_; uint64_t v___x_1542_; uint64_t v___x_1543_; uint64_t v___x_1544_; uint64_t v_fold_1545_; uint64_t v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; size_t v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_buckets_1540_ = lean_ctor_get(v_m_1538_, 1);
v___x_1541_ = lean_array_get_size(v_buckets_1540_);
v___x_1542_ = l_Lean_Elab_Tactic_Grind_instHashableDSimpCacheKey_hash(v_a_1539_);
v___x_1543_ = 32ULL;
v___x_1544_ = lean_uint64_shift_right(v___x_1542_, v___x_1543_);
v_fold_1545_ = lean_uint64_xor(v___x_1542_, v___x_1544_);
v___x_1546_ = 16ULL;
v___x_1547_ = lean_uint64_shift_right(v_fold_1545_, v___x_1546_);
v___x_1548_ = lean_uint64_xor(v_fold_1545_, v___x_1547_);
v___x_1549_ = lean_uint64_to_usize(v___x_1548_);
v___x_1550_ = lean_usize_of_nat(v___x_1541_);
v___x_1551_ = ((size_t)1ULL);
v___x_1552_ = lean_usize_sub(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_usize_land(v___x_1549_, v___x_1552_);
v___x_1554_ = lean_array_uget_borrowed(v_buckets_1540_, v___x_1553_);
v___x_1555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1539_, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg___boxed(lean_object* v_m_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1556_, v_a_1557_);
lean_dec_ref(v_a_1557_);
lean_dec_ref(v_m_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(uint8_t v___x_1559_, uint8_t v___x_1560_, lean_object* v_as_1561_, size_t v_i_1562_, size_t v_stop_1563_, lean_object* v_b_1564_){
_start:
{
lean_object* v___y_1566_; uint8_t v___x_1570_; 
v___x_1570_ = lean_usize_dec_eq(v_i_1562_, v_stop_1563_);
if (v___x_1570_ == 0)
{
lean_object* v_fst_1571_; uint8_t v___x_1572_; 
v_fst_1571_ = lean_ctor_get(v_b_1564_, 0);
v___x_1572_ = lean_unbox(v_fst_1571_);
if (v___x_1572_ == 0)
{
lean_object* v_snd_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1581_; 
v_snd_1573_ = lean_ctor_get(v_b_1564_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_b_1564_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_b_1564_, 0);
lean_dec(v_unused_1582_);
v___x_1575_ = v_b_1564_;
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_snd_1573_);
lean_dec(v_b_1564_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(v___x_1559_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1577_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_snd_1573_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v___y_1566_ = v___x_1579_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1593_; 
v_snd_1583_ = lean_ctor_get(v_b_1564_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_b_1564_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_b_1564_, 0);
lean_dec(v_unused_1594_);
v___x_1585_ = v_b_1564_;
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_dec(v_b_1564_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1587_ = lean_array_uget_borrowed(v_as_1561_, v_i_1562_);
lean_inc(v___x_1587_);
v___x_1588_ = lean_array_push(v_snd_1583_, v___x_1587_);
v___x_1589_ = lean_box(v___x_1560_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___x_1588_);
lean_ctor_set(v___x_1585_, 0, v___x_1589_);
v___x_1591_ = v___x_1585_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1588_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
v___y_1566_ = v___x_1591_;
goto v___jp_1565_;
}
}
}
}
else
{
return v_b_1564_;
}
v___jp_1565_:
{
size_t v___x_1567_; size_t v___x_1568_; 
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1562_, v___x_1567_);
v_i_1562_ = v___x_1568_;
v_b_1564_ = v___y_1566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6___boxed(lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_as_1597_, lean_object* v_i_1598_, lean_object* v_stop_1599_, lean_object* v_b_1600_){
_start:
{
uint8_t v___x_9231__boxed_1601_; uint8_t v___x_9232__boxed_1602_; size_t v_i_boxed_1603_; size_t v_stop_boxed_1604_; lean_object* v_res_1605_; 
v___x_9231__boxed_1601_ = lean_unbox(v___x_1595_);
v___x_9232__boxed_1602_ = lean_unbox(v___x_1596_);
v_i_boxed_1603_ = lean_unbox_usize(v_i_1598_);
lean_dec(v_i_1598_);
v_stop_boxed_1604_ = lean_unbox_usize(v_stop_1599_);
lean_dec(v_stop_1599_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_9231__boxed_1601_, v___x_9232__boxed_1602_, v_as_1597_, v_i_boxed_1603_, v_stop_boxed_1604_, v_b_1600_);
lean_dec_ref(v_as_1597_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(size_t v_sz_1606_, size_t v_i_1607_, lean_object* v_bs_1608_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1607_, v_sz_1606_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_bs_1608_);
return v___x_1610_;
}
else
{
lean_object* v_v_1611_; lean_object* v___x_1612_; lean_object* v_bs_x27_1613_; size_t v___x_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v_v_1611_ = lean_array_uget(v_bs_1608_, v_i_1607_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v_bs_x27_1613_ = lean_array_uset(v_bs_1608_, v_i_1607_, v___x_1612_);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_add(v_i_1607_, v___x_1614_);
v___x_1616_ = lean_array_uset(v_bs_x27_1613_, v_i_1607_, v_v_1611_);
v_i_1607_ = v___x_1615_;
v_bs_1608_ = v___x_1616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5___boxed(lean_object* v_sz_1618_, lean_object* v_i_1619_, lean_object* v_bs_1620_){
_start:
{
size_t v_sz_boxed_1621_; size_t v_i_boxed_1622_; lean_object* v_res_1623_; 
v_sz_boxed_1621_ = lean_unbox_usize(v_sz_1618_);
lean_dec(v_sz_1618_);
v_i_boxed_1622_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_boxed_1621_, v_i_boxed_1622_, v_bs_1620_);
return v_res_1623_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__0));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__4));
v___x_1634_ = l_Lean_mkConst(v___x_1633_, v___x_1632_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12(void){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1646_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__12);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__13);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1649_);
lean_ctor_set(v___x_1651_, 2, v___x_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(lean_object* v_stx_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_1655_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1890_; 
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v___x_1787_, 0);
lean_dec(v_unused_1891_);
v___x_1789_ = v___x_1787_;
v_isShared_1790_ = v_isSharedCheck_1890_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v___x_1787_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1890_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
lean_inc(v_stx_1654_);
v___x_1792_ = l_Lean_Syntax_isOfKind(v_stx_1654_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; 
lean_del_object(v___x_1789_);
lean_dec(v_stx_1654_);
v___x_1793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1824_; lean_object* v_args_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___x_1852_; lean_object* v_variantId_x3f_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1881_ = l_Lean_Syntax_getArg(v_stx_1654_, v___x_1852_);
v___x_1882_ = l_Lean_Syntax_isNone(v___x_1881_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1883_; 
lean_inc(v___x_1881_);
v___x_1883_ = l_Lean_Syntax_matchesNull(v___x_1881_, v___x_1852_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec(v___x_1881_);
lean_del_object(v___x_1789_);
lean_dec(v_stx_1654_);
v___x_1884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = l_Lean_Syntax_getArg(v___x_1881_, v___x_1794_);
lean_dec(v___x_1881_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 1);
lean_ctor_set(v___x_1789_, 0, v___x_1885_);
v___x_1887_ = v___x_1789_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v_variantId_x3f_1854_ = v___x_1887_;
v___y_1855_ = v___y_1655_;
v___y_1856_ = v___y_1656_;
v___y_1857_ = v___y_1657_;
v___y_1858_ = v___y_1658_;
v___y_1859_ = v___y_1659_;
v___y_1860_ = v___y_1660_;
v___y_1861_ = v___y_1661_;
v___y_1862_ = v___y_1662_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v___x_1889_; 
lean_dec(v___x_1881_);
lean_del_object(v___x_1789_);
v___x_1889_ = lean_box(0);
v_variantId_x3f_1854_ = v___x_1889_;
v___y_1855_ = v___y_1655_;
v___y_1856_ = v___y_1656_;
v___y_1857_ = v___y_1657_;
v___y_1858_ = v___y_1658_;
v___y_1859_ = v___y_1659_;
v___y_1860_ = v___y_1660_;
v___y_1861_ = v___y_1661_;
v___y_1862_ = v___y_1662_;
goto v___jp_1853_;
}
v___jp_1795_:
{
lean_object* v___x_1806_; 
v___x_1806_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs(v___y_1798_, v___y_1799_, v___y_1804_, v___y_1803_, v___y_1800_, v___y_1802_, v___y_1797_, v___y_1801_, v___y_1796_);
lean_dec(v___y_1798_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_cache_1810_; lean_object* v_dsimpState_1811_; lean_object* v___x_1812_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc_n(v_a_1807_, 2);
lean_dec_ref_known(v___x_1806_, 1);
lean_inc(v___y_1805_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___y_1805_);
lean_ctor_set(v___x_1808_, 1, v_a_1807_);
v___x_1809_ = lean_st_ref_get(v___y_1804_);
v_cache_1810_ = lean_ctor_get(v___x_1809_, 3);
lean_inc_ref(v_cache_1810_);
lean_dec(v___x_1809_);
v_dsimpState_1811_ = lean_ctor_get(v_cache_1810_, 3);
lean_inc_ref(v_dsimpState_1811_);
lean_dec_ref(v_cache_1810_);
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_dsimpState_1811_, v___x_1808_);
lean_dec_ref(v_dsimpState_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__14);
v___y_1665_ = v___y_1805_;
v___y_1666_ = v___y_1796_;
v___y_1667_ = v___y_1797_;
v___y_1668_ = v___y_1799_;
v___y_1669_ = v___y_1800_;
v___y_1670_ = v___y_1801_;
v___y_1671_ = v___y_1802_;
v___y_1672_ = v___y_1803_;
v___y_1673_ = v_a_1807_;
v___y_1674_ = v___x_1808_;
v___y_1675_ = v___y_1804_;
v___y_1676_ = v___x_1813_;
goto v___jp_1664_;
}
else
{
lean_object* v_val_1814_; 
v_val_1814_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v___x_1812_, 1);
v___y_1665_ = v___y_1805_;
v___y_1666_ = v___y_1796_;
v___y_1667_ = v___y_1797_;
v___y_1668_ = v___y_1799_;
v___y_1669_ = v___y_1800_;
v___y_1670_ = v___y_1801_;
v___y_1671_ = v___y_1802_;
v___y_1672_ = v___y_1803_;
v___y_1673_ = v_a_1807_;
v___y_1674_ = v___x_1808_;
v___y_1675_ = v___y_1804_;
v___y_1676_ = v_val_1814_;
goto v___jp_1664_;
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v___y_1805_);
v_a_1815_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1806_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1806_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
v___jp_1823_:
{
if (lean_obj_tag(v___y_1824_) == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_box(0);
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1831_;
v___y_1798_ = v_args_1825_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1829_;
v___y_1801_ = v___y_1832_;
v___y_1802_ = v___y_1830_;
v___y_1803_ = v___y_1828_;
v___y_1804_ = v___y_1827_;
v___y_1805_ = v___x_1834_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1835_; lean_object* v___x_1836_; 
v_val_1835_ = lean_ctor_get(v___y_1824_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v___y_1824_, 1);
v___x_1836_ = l_Lean_TSyntax_getId(v_val_1835_);
lean_dec(v_val_1835_);
v___y_1796_ = v___y_1833_;
v___y_1797_ = v___y_1831_;
v___y_1798_ = v_args_1825_;
v___y_1799_ = v___y_1826_;
v___y_1800_ = v___y_1829_;
v___y_1801_ = v___y_1832_;
v___y_1802_ = v___y_1830_;
v___y_1803_ = v___y_1828_;
v___y_1804_ = v___y_1827_;
v___y_1805_ = v___x_1836_;
goto v___jp_1795_;
}
}
v___jp_1837_:
{
size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v_sz_1848_ = lean_array_size(v___y_1847_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__5(v_sz_1848_, v___x_1849_, v___y_1847_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1851_; 
lean_dec(v___y_1841_);
v___x_1851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1851_;
}
else
{
v___y_1824_ = v___y_1841_;
v_args_1825_ = v___x_1850_;
v___y_1826_ = v___y_1845_;
v___y_1827_ = v___y_1843_;
v___y_1828_ = v___y_1839_;
v___y_1829_ = v___y_1842_;
v___y_1830_ = v___y_1844_;
v___y_1831_ = v___y_1840_;
v___y_1832_ = v___y_1846_;
v___y_1833_ = v___y_1838_;
goto v___jp_1823_;
}
}
v___jp_1853_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = lean_unsigned_to_nat(2u);
v___x_1864_ = l_Lean_Syntax_getArg(v_stx_1654_, v___x_1863_);
lean_dec(v_stx_1654_);
v___x_1865_ = l_Lean_Syntax_isNone(v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_1864_);
v___x_1867_ = l_Lean_Syntax_matchesNull(v___x_1864_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec(v___x_1864_);
lean_dec(v_variantId_x3f_1854_);
v___x_1868_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__0___redArg();
return v___x_1868_;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1869_ = l_Lean_Syntax_getArg(v___x_1864_, v___x_1852_);
lean_dec(v___x_1864_);
v___x_1870_ = l_Lean_Syntax_getArgs(v___x_1869_);
lean_dec(v___x_1869_);
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__15));
v___x_1872_ = lean_array_get_size(v___x_1870_);
v___x_1873_ = lean_nat_dec_lt(v___x_1794_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_dec_ref(v___x_1870_);
v___y_1838_ = v___y_1862_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1860_;
v___y_1841_ = v_variantId_x3f_1854_;
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___y_1856_;
v___y_1844_ = v___y_1859_;
v___y_1845_ = v___y_1855_;
v___y_1846_ = v___y_1861_;
v___y_1847_ = v___x_1871_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; size_t v___x_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v_snd_1879_; 
v___x_1874_ = lean_box(v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1871_);
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = lean_usize_of_nat(v___x_1872_);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__6(v___x_1867_, v___x_1865_, v___x_1870_, v___x_1876_, v___x_1877_, v___x_1875_);
lean_dec_ref(v___x_1870_);
v_snd_1879_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_snd_1879_);
lean_dec_ref(v___x_1878_);
v___y_1838_ = v___y_1862_;
v___y_1839_ = v___y_1857_;
v___y_1840_ = v___y_1860_;
v___y_1841_ = v_variantId_x3f_1854_;
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___y_1856_;
v___y_1844_ = v___y_1859_;
v___y_1845_ = v___y_1855_;
v___y_1846_ = v___y_1861_;
v___y_1847_ = v_snd_1879_;
goto v___jp_1837_;
}
}
}
else
{
lean_object* v___x_1880_; 
lean_dec(v___x_1864_);
v___x_1880_ = lean_box(0);
v___y_1824_ = v_variantId_x3f_1854_;
v_args_1825_ = v___x_1880_;
v___y_1826_ = v___y_1855_;
v___y_1827_ = v___y_1856_;
v___y_1828_ = v___y_1857_;
v___y_1829_ = v___y_1858_;
v___y_1830_ = v___y_1859_;
v___y_1831_ = v___y_1860_;
v___y_1832_ = v___y_1861_;
v___y_1833_ = v___y_1862_;
goto v___jp_1823_;
}
}
}
}
}
else
{
lean_dec(v_stx_1654_);
return v___x_1787_;
}
v___jp_1664_:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpVariant(v___y_1665_, v___y_1673_, v___y_1668_, v___y_1675_, v___y_1672_, v___y_1669_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v_fst_1679_; lean_object* v_snd_1680_; lean_object* v___x_1681_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v_fst_1679_ = lean_ctor_get(v_a_1678_, 0);
lean_inc(v_fst_1679_);
v_snd_1680_ = lean_ctor_get(v_a_1678_, 1);
lean_inc(v_snd_1680_);
lean_dec(v_a_1678_);
v___x_1681_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1675_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v_toGoalState_1683_; lean_object* v_mvarId_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1770_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v_toGoalState_1683_ = lean_ctor_get(v_a_1682_, 0);
v_mvarId_1684_ = lean_ctor_get(v_a_1682_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_a_1682_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1686_ = v_a_1682_;
v_isShared_1687_ = v_isSharedCheck_1770_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_mvarId_1684_);
lean_inc(v_toGoalState_1683_);
lean_dec(v_a_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1770_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_inc_n(v_mvarId_1684_, 2);
v___f_1688_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1688_, 0, v_mvarId_1684_);
lean_closure_set(v___f_1688_, 1, v_fst_1679_);
lean_closure_set(v___f_1688_, 2, v_snd_1680_);
lean_closure_set(v___f_1688_, 3, v___y_1676_);
v___x_1689_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__1___boxed), 13, 3);
lean_closure_set(v___x_1689_, 0, lean_box(0));
lean_closure_set(v___x_1689_, 1, v_mvarId_1684_);
lean_closure_set(v___x_1689_, 2, v___f_1688_);
v___x_1690_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1689_, v___y_1668_, v___y_1675_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v_fst_1692_; lean_object* v_snd_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1761_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v_fst_1692_ = lean_ctor_get(v_a_1691_, 0);
v_snd_1693_ = lean_ctor_get(v_a_1691_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1695_ = v_a_1691_;
v_isShared_1696_ = v_isSharedCheck_1761_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_snd_1693_);
lean_inc(v_fst_1692_);
lean_dec(v_a_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1761_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v_cache_1698_; lean_object* v_symState_1699_; lean_object* v_grindState_1700_; lean_object* v_goals_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1760_; 
v___x_1697_ = lean_st_ref_take(v___y_1675_);
v_cache_1698_ = lean_ctor_get(v___x_1697_, 3);
v_symState_1699_ = lean_ctor_get(v___x_1697_, 0);
v_grindState_1700_ = lean_ctor_get(v___x_1697_, 1);
v_goals_1701_ = lean_ctor_get(v___x_1697_, 2);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1703_ = v___x_1697_;
v_isShared_1704_ = v_isSharedCheck_1760_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_cache_1698_);
lean_inc(v_goals_1701_);
lean_inc(v_grindState_1700_);
lean_inc(v_symState_1699_);
lean_dec(v___x_1697_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1760_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_backwardRuleName_1705_; lean_object* v_backwardRuleSyntax_1706_; lean_object* v_simpState_1707_; lean_object* v_dsimpState_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1759_; 
v_backwardRuleName_1705_ = lean_ctor_get(v_cache_1698_, 0);
v_backwardRuleSyntax_1706_ = lean_ctor_get(v_cache_1698_, 1);
v_simpState_1707_ = lean_ctor_get(v_cache_1698_, 2);
v_dsimpState_1708_ = lean_ctor_get(v_cache_1698_, 3);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_cache_1698_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1710_ = v_cache_1698_;
v_isShared_1711_ = v_isSharedCheck_1759_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_dsimpState_1708_);
lean_inc(v_simpState_1707_);
lean_inc(v_backwardRuleSyntax_1706_);
lean_inc(v_backwardRuleName_1705_);
lean_dec(v_cache_1698_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1759_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_dsimpState_1708_, v___y_1674_, v_snd_1693_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 3, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_backwardRuleName_1705_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_backwardRuleSyntax_1706_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_simpState_1707_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 3, v___x_1714_);
v___x_1716_ = v___x_1703_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_symState_1699_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_grindState_1700_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_goals_1701_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_st_ref_put(v___y_1675_, v___x_1716_);
if (lean_obj_tag(v_fst_1692_) == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref_known(v_fst_1692_, 0);
lean_del_object(v___x_1695_);
lean_del_object(v___x_1686_);
lean_dec(v_mvarId_1684_);
lean_dec_ref(v_toGoalState_1683_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__1);
v___x_1719_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_elabDSimpArgs_spec__2___redArg(v___x_1718_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
return v___x_1719_;
}
else
{
lean_object* v_e_x27_1720_; uint8_t v___x_1721_; 
v_e_x27_1720_ = lean_ctor_get(v_fst_1692_, 0);
lean_inc_ref(v_e_x27_1720_);
lean_dec_ref_known(v_fst_1692_, 1);
v___x_1721_ = l_Lean_Expr_isTrue(v_e_x27_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_inc(v_mvarId_1684_);
v___x_1722_ = l_Lean_MVarId_getDecl(v_mvarId_1684_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v_userName_1724_; lean_object* v___x_1725_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v_userName_1724_ = lean_ctor_get(v_a_1723_, 0);
lean_inc(v_userName_1724_);
lean_dec(v_a_1723_);
v___x_1725_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_1720_, v_userName_1724_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_n(v_a_1726_, 2);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1684_, v_a_1726_, v___y_1667_);
lean_dec_ref(v___x_1727_);
v___x_1728_ = l_Lean_Expr_mvarId_x21(v_a_1726_);
lean_dec(v_a_1726_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1728_);
v___x_1730_ = v___x_1686_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_toGoalState_1683_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = lean_box(0);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 1, v___x_1731_);
lean_ctor_set(v___x_1695_, 0, v___x_1730_);
v___x_1733_ = v___x_1695_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1733_, v___y_1675_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_del_object(v___x_1695_);
lean_del_object(v___x_1686_);
lean_dec(v_mvarId_1684_);
lean_dec_ref(v_toGoalState_1683_);
v_a_1737_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1725_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_e_x27_1720_);
lean_del_object(v___x_1695_);
lean_del_object(v___x_1686_);
lean_dec(v_mvarId_1684_);
lean_dec_ref(v_toGoalState_1683_);
v_a_1745_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1722_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1722_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec_ref(v_e_x27_1720_);
lean_del_object(v___x_1695_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_toGoalState_1683_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5, &l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__5);
v___x_1755_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1684_, v___x_1754_, v___y_1667_);
lean_dec_ref(v___x_1755_);
v___x_1756_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1753_, v___y_1675_, v___y_1671_, v___y_1667_, v___y_1670_, v___y_1666_);
return v___x_1756_;
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
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1686_);
lean_dec(v_mvarId_1684_);
lean_dec_ref(v_toGoalState_1683_);
lean_dec_ref(v___y_1674_);
v_a_1762_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1690_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1690_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_snd_1680_);
lean_dec(v_fst_1679_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___y_1674_);
v_a_1771_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1681_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1681_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___y_1674_);
v_a_1779_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1677_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1677_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed(lean_object* v_stx_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1(v_stx_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(lean_object* v_stx_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; 
v___f_1913_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1913_, 0, v_stx_1903_);
v___x_1914_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1913_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed(lean_object* v_stx_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp(v_stx_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2(lean_object* v_00_u03b2_1926_, lean_object* v_m_1927_, lean_object* v_a_1928_, lean_object* v_b_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2___redArg(v_m_1927_, v_a_1928_, v_b_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(lean_object* v_mvarId_1931_, lean_object* v_val_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___redArg(v_mvarId_1931_, v_val_1932_, v___y_1938_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3___boxed(lean_object* v_mvarId_1943_, lean_object* v_val_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3(v_mvarId_1943_, v_val_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(lean_object* v_00_u03b2_1955_, lean_object* v_m_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___redArg(v_m_1956_, v_a_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4___boxed(lean_object* v_00_u03b2_1959_, lean_object* v_m_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4(v_00_u03b2_1959_, v_m_1960_, v_a_1961_);
lean_dec_ref(v_a_1961_);
lean_dec_ref(v_m_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(lean_object* v_00_u03b2_1963_, lean_object* v_a_1964_, lean_object* v_x_1965_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___redArg(v_a_1964_, v_x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1967_, lean_object* v_a_1968_, lean_object* v_x_1969_){
_start:
{
uint8_t v_res_1970_; lean_object* v_r_1971_; 
v_res_1970_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__2(v_00_u03b2_1967_, v_a_1968_, v_x_1969_);
lean_dec(v_x_1969_);
lean_dec_ref(v_a_1968_);
v_r_1971_ = lean_box(v_res_1970_);
return v_r_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3(lean_object* v_00_u03b2_1972_, lean_object* v_data_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3___redArg(v_data_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4(lean_object* v_00_u03b2_1975_, lean_object* v_a_1976_, lean_object* v_b_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__4___redArg(v_a_1976_, v_b_1977_, v_x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6(lean_object* v_00_u03b2_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6___redArg(v_x_1981_, v_x_1982_, v_x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(lean_object* v_00_u03b2_1985_, lean_object* v_a_1986_, lean_object* v_x_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___redArg(v_a_1986_, v_x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1989_, lean_object* v_a_1990_, lean_object* v_x_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__4_spec__8(v_00_u03b2_1989_, v_a_1990_, v_x_1991_);
lean_dec(v_x_1991_);
lean_dec_ref(v_a_1990_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1993_, lean_object* v_i_1994_, lean_object* v_source_1995_, lean_object* v_target_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4___redArg(v_i_1994_, v_source_1995_, v_target_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1998_, lean_object* v_x_1999_, size_t v_x_2000_, size_t v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___redArg(v_x_1999_, v_x_2000_, v_x_2001_, v_x_2002_, v_x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
size_t v_x_9928__boxed_2011_; size_t v_x_9929__boxed_2012_; lean_object* v_res_2013_; 
v_x_9928__boxed_2011_ = lean_unbox_usize(v_x_2007_);
lean_dec(v_x_2007_);
v_x_9929__boxed_2012_ = lean_unbox_usize(v_x_2008_);
lean_dec(v_x_2008_);
v_res_2013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8(v_00_u03b2_2005_, v_x_2006_, v_x_9928__boxed_2011_, v_x_9929__boxed_2012_, v_x_2009_, v_x_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2015_, v_x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_2018_, lean_object* v_n_2019_, lean_object* v_k_2020_, lean_object* v_v_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13___redArg(v_n_2019_, v_k_2020_, v_v_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_2023_, size_t v_depth_2024_, lean_object* v_keys_2025_, lean_object* v_vals_2026_, lean_object* v_heq_2027_, lean_object* v_i_2028_, lean_object* v_entries_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___redArg(v_depth_2024_, v_keys_2025_, v_vals_2026_, v_i_2028_, v_entries_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_2031_, lean_object* v_depth_2032_, lean_object* v_keys_2033_, lean_object* v_vals_2034_, lean_object* v_heq_2035_, lean_object* v_i_2036_, lean_object* v_entries_2037_){
_start:
{
size_t v_depth_boxed_2038_; lean_object* v_res_2039_; 
v_depth_boxed_2038_ = lean_unbox_usize(v_depth_2032_);
lean_dec(v_depth_2032_);
v_res_2039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__14(v_00_u03b2_2031_, v_depth_boxed_2038_, v_keys_2033_, v_vals_2034_, v_heq_2035_, v_i_2036_, v_entries_2037_);
lean_dec_ref(v_vals_2034_);
lean_dec_ref(v_keys_2033_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15(lean_object* v_00_u03b2_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp_spec__3_spec__6_spec__8_spec__13_spec__15___redArg(v_x_2041_, v_x_2042_, v_x_2043_, v_x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1(){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2087_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___lam__1___closed__11));
v___x_2089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___closed__15));
v___x_2090_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___boxed), 10, 0);
v___x_2091_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2087_, v___x_2088_, v___x_2089_, v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1___boxed(lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_DSimp_0__Lean_Elab_Tactic_Grind_evalSymDSimp__1();
return v_res_2093_;
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
