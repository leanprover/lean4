// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
// Imports: public import Lean.Elab.Tactic.Do.Attr public import Lean.Meta.Sym.Pattern import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Meta.DiscrTree.Util
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default;
extern lean_object* l_Lean_Meta_Sym_instInhabitedPattern_default;
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_triple_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_triple_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_simp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_simp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "conclusion is not a Triple "};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(31, 48, 165, 224, 255, 99, 7, 166)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "unexpected kind of spec theorem; not a triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PostShape"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "args"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 175, 203, 13, 190, 221, 208, 89)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(91, 155, 250, 91, 111, 213, 166, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid 'spec', proposition expected"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "conclusion is not an equality"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4(lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__16_spec__28(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__16(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Failed to migrate simp spec "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Failed to migrate unfold spec "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_etaPotential_8_; lean_object* v___x_9_; 
v_etaPotential_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_etaPotential_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_etaPotential_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_triple_elim___redArg(lean_object* v_t_22_, lean_object* v_triple_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_22_, v_triple_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_triple_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_triple_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_26_, v_triple_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_simp_elim___redArg(lean_object* v_t_30_, lean_object* v_simp_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_30_, v_simp_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_simp_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_simp_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_34_, v_simp_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_42_ = lean_unsigned_to_nat(1000u);
v___x_43_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default));
v___x_44_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default;
v___x_45_ = l_Lean_Meta_Sym_instInhabitedPattern_default;
v___x_46_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
lean_ctor_set(v___x_46_, 2, v___x_43_);
lean_ctor_set(v___x_46_, 3, v___x_42_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default;
return v___x_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0(lean_object* v_thm_u2081_49_, lean_object* v_thm_u2082_50_){
_start:
{
lean_object* v_proof_51_; lean_object* v_proof_52_; uint8_t v___x_53_; 
v_proof_51_ = lean_ctor_get(v_thm_u2081_49_, 1);
lean_inc_ref(v_proof_51_);
lean_dec_ref(v_thm_u2081_49_);
v_proof_52_ = lean_ctor_get(v_thm_u2082_50_, 1);
lean_inc_ref(v_proof_52_);
lean_dec_ref(v_thm_u2082_50_);
v___x_53_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_51_, v_proof_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0___boxed(lean_object* v_thm_u2081_54_, lean_object* v_thm_u2082_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0(v_thm_u2081_54_, v_thm_u2082_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(lean_object* v_as_60_, size_t v_i_61_, size_t v_stop_62_, lean_object* v_b_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_usize_dec_eq(v_i_61_, v_stop_62_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_array_uget_borrowed(v_as_60_, v_i_61_);
lean_inc(v___x_70_);
v___x_71_ = l_Lean_Meta_mkCongrFun(v_b_63_, v___x_70_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; size_t v___x_73_; size_t v___x_74_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_add(v_i_61_, v___x_73_);
v_i_61_ = v___x_74_;
v_b_63_ = v_a_72_;
goto _start;
}
else
{
return v___x_71_;
}
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v_b_63_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0___boxed(lean_object* v_as_77_, lean_object* v_i_78_, lean_object* v_stop_79_, lean_object* v_b_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; lean_object* v_res_88_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_78_);
lean_dec(v_i_78_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_79_);
lean_dec(v_stop_79_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(v_as_77_, v_i_boxed_86_, v_stop_boxed_87_, v_b_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_as_77_);
return v_res_88_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2(void){
_start:
{
uint8_t v___x_92_; uint64_t v___x_93_; 
v___x_92_ = 2;
v___x_93_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate(lean_object* v_specThm_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_proof_100_; lean_object* v_kind_101_; lean_object* v___x_102_; 
v_proof_100_ = lean_ctor_get(v_specThm_94_, 1);
lean_inc_ref(v_proof_100_);
v_kind_101_ = lean_ctor_get(v_specThm_94_, 2);
lean_inc_ref(v_kind_101_);
lean_dec_ref(v_specThm_94_);
v___x_102_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(v_proof_100_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_snd_104_; lean_object* v_snd_105_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
v_snd_104_ = lean_ctor_get(v_a_103_, 1);
lean_inc(v_snd_104_);
v_snd_105_ = lean_ctor_get(v_snd_104_, 1);
lean_inc(v_snd_105_);
if (lean_obj_tag(v_kind_101_) == 1)
{
lean_object* v_fst_106_; lean_object* v_fst_107_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_244_; 
v_fst_106_ = lean_ctor_get(v_a_103_, 0);
lean_inc(v_fst_106_);
lean_dec(v_a_103_);
v_fst_107_ = lean_ctor_get(v_snd_104_, 0);
lean_inc(v_fst_107_);
lean_dec(v_snd_104_);
v_fst_108_ = lean_ctor_get(v_snd_105_, 0);
v_snd_109_ = lean_ctor_get(v_snd_105_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_snd_105_);
if (v_isSharedCheck_244_ == 0)
{
v___x_111_ = v_snd_105_;
v_isShared_112_ = v_isSharedCheck_244_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_snd_109_);
lean_inc(v_fst_108_);
lean_dec(v_snd_105_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_244_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_etaArgs_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_etaArgs_113_ = lean_ctor_get(v_kind_101_, 0);
lean_inc(v_etaArgs_113_);
lean_dec_ref(v_kind_101_);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_nat_dec_eq(v_etaArgs_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = l_Lean_Expr_cleanupAnnotations(v_snd_109_);
v___x_117_ = l_Lean_Expr_isApp(v___x_116_);
if (v___x_117_ == 0)
{
lean_dec_ref(v___x_116_);
lean_dec(v_etaArgs_113_);
lean_del_object(v___x_111_);
lean_dec(v_fst_108_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
return v___x_102_;
}
else
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_116_);
v___x_119_ = l_Lean_Expr_isApp(v___x_118_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___x_118_);
lean_dec(v_etaArgs_113_);
lean_del_object(v___x_111_);
lean_dec(v_fst_108_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
return v___x_102_;
}
else
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_118_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v___x_120_);
lean_dec(v_etaArgs_113_);
lean_del_object(v___x_111_);
lean_dec(v_fst_108_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
return v___x_102_;
}
else
{
lean_object* v_arg_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_arg_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_arg_122_);
v___x_123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_124_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1));
v___x_125_ = l_Lean_Expr_isConstOf(v___x_123_, v___x_124_);
lean_dec_ref(v___x_123_);
if (v___x_125_ == 0)
{
lean_dec_ref(v_arg_122_);
lean_dec(v_etaArgs_113_);
lean_del_object(v___x_111_);
lean_dec(v_fst_108_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
return v___x_102_;
}
else
{
lean_object* v___x_126_; uint8_t v_foApprox_127_; uint8_t v_ctxApprox_128_; uint8_t v_quasiPatternApprox_129_; uint8_t v_constApprox_130_; uint8_t v_isDefEqStuckEx_131_; uint8_t v_unificationHints_132_; uint8_t v_proofIrrelevance_133_; uint8_t v_assignSyntheticOpaque_134_; uint8_t v_offsetCnstrs_135_; uint8_t v_etaStruct_136_; uint8_t v_univApprox_137_; uint8_t v_iota_138_; uint8_t v_beta_139_; uint8_t v_proj_140_; uint8_t v_zeta_141_; uint8_t v_zetaDelta_142_; uint8_t v_zetaUnused_143_; uint8_t v_zetaHave_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v___x_102_);
v___x_126_ = l_Lean_Meta_Context_config(v_a_95_);
v_foApprox_127_ = lean_ctor_get_uint8(v___x_126_, 0);
v_ctxApprox_128_ = lean_ctor_get_uint8(v___x_126_, 1);
v_quasiPatternApprox_129_ = lean_ctor_get_uint8(v___x_126_, 2);
v_constApprox_130_ = lean_ctor_get_uint8(v___x_126_, 3);
v_isDefEqStuckEx_131_ = lean_ctor_get_uint8(v___x_126_, 4);
v_unificationHints_132_ = lean_ctor_get_uint8(v___x_126_, 5);
v_proofIrrelevance_133_ = lean_ctor_get_uint8(v___x_126_, 6);
v_assignSyntheticOpaque_134_ = lean_ctor_get_uint8(v___x_126_, 7);
v_offsetCnstrs_135_ = lean_ctor_get_uint8(v___x_126_, 8);
v_etaStruct_136_ = lean_ctor_get_uint8(v___x_126_, 10);
v_univApprox_137_ = lean_ctor_get_uint8(v___x_126_, 11);
v_iota_138_ = lean_ctor_get_uint8(v___x_126_, 12);
v_beta_139_ = lean_ctor_get_uint8(v___x_126_, 13);
v_proj_140_ = lean_ctor_get_uint8(v___x_126_, 14);
v_zeta_141_ = lean_ctor_get_uint8(v___x_126_, 15);
v_zetaDelta_142_ = lean_ctor_get_uint8(v___x_126_, 16);
v_zetaUnused_143_ = lean_ctor_get_uint8(v___x_126_, 17);
v_zetaHave_144_ = lean_ctor_get_uint8(v___x_126_, 18);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_243_ == 0)
{
v___x_146_ = v___x_126_;
v_isShared_147_ = v_isSharedCheck_243_;
goto v_resetjp_145_;
}
else
{
lean_dec(v___x_126_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_243_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint8_t v_trackZetaDelta_148_; lean_object* v_zetaDeltaSet_149_; lean_object* v_lctx_150_; lean_object* v_localInstances_151_; lean_object* v_defEqCtx_x3f_152_; lean_object* v_synthPendingDepth_153_; lean_object* v_canUnfold_x3f_154_; uint8_t v_univApprox_155_; uint8_t v_inTypeClassResolution_156_; uint8_t v_cacheInferType_157_; uint8_t v___x_158_; lean_object* v_config_160_; 
v_trackZetaDelta_148_ = lean_ctor_get_uint8(v_a_95_, sizeof(void*)*7);
v_zetaDeltaSet_149_ = lean_ctor_get(v_a_95_, 1);
v_lctx_150_ = lean_ctor_get(v_a_95_, 2);
v_localInstances_151_ = lean_ctor_get(v_a_95_, 3);
v_defEqCtx_x3f_152_ = lean_ctor_get(v_a_95_, 4);
v_synthPendingDepth_153_ = lean_ctor_get(v_a_95_, 5);
v_canUnfold_x3f_154_ = lean_ctor_get(v_a_95_, 6);
v_univApprox_155_ = lean_ctor_get_uint8(v_a_95_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_156_ = lean_ctor_get_uint8(v_a_95_, sizeof(void*)*7 + 2);
v_cacheInferType_157_ = lean_ctor_get_uint8(v_a_95_, sizeof(void*)*7 + 3);
v___x_158_ = 2;
if (v_isShared_147_ == 0)
{
v_config_160_ = v___x_146_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 0, v_foApprox_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 1, v_ctxApprox_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 2, v_quasiPatternApprox_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 3, v_constApprox_130_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 4, v_isDefEqStuckEx_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 5, v_unificationHints_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 6, v_proofIrrelevance_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 7, v_assignSyntheticOpaque_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 8, v_offsetCnstrs_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 10, v_etaStruct_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 11, v_univApprox_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 12, v_iota_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 13, v_beta_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 14, v_proj_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 15, v_zeta_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 16, v_zetaDelta_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 17, v_zetaUnused_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, 18, v_zetaHave_144_);
v_config_160_ = v_reuseFailAlloc_242_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v___x_163_; uint8_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v_key_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
lean_ctor_set_uint8(v_config_160_, 9, v___x_158_);
v___x_161_ = l_Lean_Meta_Context_configKey(v_a_95_);
v___x_162_ = 2ULL;
v___x_163_ = lean_uint64_shift_right(v___x_161_, v___x_162_);
v___x_164_ = 0;
v___x_165_ = lean_uint64_shift_left(v___x_163_, v___x_162_);
v___x_166_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2);
v_key_167_ = lean_uint64_lor(v___x_165_, v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_168_, 0, v_config_160_);
lean_ctor_set_uint64(v___x_168_, sizeof(void*)*1, v_key_167_);
lean_inc(v_canUnfold_x3f_154_);
lean_inc(v_synthPendingDepth_153_);
lean_inc(v_defEqCtx_x3f_152_);
lean_inc_ref(v_localInstances_151_);
lean_inc_ref(v_lctx_150_);
lean_inc(v_zetaDeltaSet_149_);
v___x_169_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_zetaDeltaSet_149_);
lean_ctor_set(v___x_169_, 2, v_lctx_150_);
lean_ctor_set(v___x_169_, 3, v_localInstances_151_);
lean_ctor_set(v___x_169_, 4, v_defEqCtx_x3f_152_);
lean_ctor_set(v___x_169_, 5, v_synthPendingDepth_153_);
lean_ctor_set(v___x_169_, 6, v_canUnfold_x3f_154_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7, v_trackZetaDelta_148_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7 + 1, v_univApprox_155_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7 + 2, v_inTypeClassResolution_156_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*7 + 3, v_cacheInferType_157_);
v___x_170_ = l_Lean_Meta_forallMetaBoundedTelescope(v_arg_122_, v_etaArgs_113_, v___x_164_, v___x_169_, v_a_96_, v_a_97_, v_a_98_);
lean_dec_ref(v___x_169_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v_snd_172_; lean_object* v_fst_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_233_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v_snd_172_ = lean_ctor_get(v_a_171_, 1);
v_fst_173_ = lean_ctor_get(v_a_171_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_233_ == 0)
{
v___x_175_ = v_a_171_;
v_isShared_176_ = v_isSharedCheck_233_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_172_);
lean_inc(v_fst_173_);
lean_dec(v_a_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_233_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_fst_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_231_; 
v_fst_177_ = lean_ctor_get(v_snd_172_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_snd_172_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v_snd_172_, 1);
lean_dec(v_unused_232_);
v___x_179_ = v_snd_172_;
v_isShared_180_ = v_isSharedCheck_231_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_fst_177_);
lean_dec(v_snd_172_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_231_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_a_182_; lean_object* v___y_212_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_array_get_size(v_fst_173_);
v___x_223_ = lean_nat_dec_lt(v___x_114_, v___x_222_);
if (v___x_223_ == 0)
{
v_a_182_ = v_fst_108_;
goto v___jp_181_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = lean_nat_dec_le(v___x_222_, v___x_222_);
if (v___x_224_ == 0)
{
if (v___x_223_ == 0)
{
v_a_182_ = v_fst_108_;
goto v___jp_181_;
}
else
{
size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v___x_225_ = ((size_t)0ULL);
v___x_226_ = lean_usize_of_nat(v___x_222_);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(v_fst_173_, v___x_225_, v___x_226_, v_fst_108_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
v___y_212_ = v___x_227_;
goto v___jp_211_;
}
}
else
{
size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; 
v___x_228_ = ((size_t)0ULL);
v___x_229_ = lean_usize_of_nat(v___x_222_);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(v_fst_173_, v___x_228_, v___x_229_, v_fst_108_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
v___y_212_ = v___x_230_;
goto v___jp_211_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; 
lean_inc(v_a_98_);
lean_inc_ref(v_a_97_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
lean_inc_ref(v_a_182_);
v___x_183_ = lean_infer_type(v_a_182_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_202_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_202_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_202_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_202_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = l_Array_append___redArg(v_fst_106_, v_fst_173_);
lean_dec(v_fst_173_);
v___x_189_ = l_Array_append___redArg(v_fst_107_, v_fst_177_);
lean_dec(v_fst_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_a_184_);
lean_ctor_set(v___x_179_, 0, v_a_182_);
v___x_191_ = v___x_179_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_182_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_a_184_);
v___x_191_ = v_reuseFailAlloc_201_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_191_);
lean_ctor_set(v___x_175_, 0, v___x_189_);
v___x_193_ = v___x_175_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_200_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___x_193_);
lean_ctor_set(v___x_111_, 0, v___x_188_);
v___x_195_ = v___x_111_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_195_);
v___x_197_ = v___x_186_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_a_182_);
lean_del_object(v___x_179_);
lean_dec(v_fst_177_);
lean_del_object(v___x_175_);
lean_dec(v_fst_173_);
lean_del_object(v___x_111_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
v_a_203_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_183_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_183_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
v___jp_211_:
{
if (lean_obj_tag(v___y_212_) == 0)
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___y_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___y_212_);
v_a_182_ = v_a_213_;
goto v___jp_181_;
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_del_object(v___x_179_);
lean_dec(v_fst_177_);
lean_del_object(v___x_175_);
lean_dec(v_fst_173_);
lean_del_object(v___x_111_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
v_a_214_ = lean_ctor_get(v___y_212_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___y_212_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___y_212_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___y_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_del_object(v___x_111_);
lean_dec(v_fst_108_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
v_a_234_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_170_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_170_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
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
else
{
lean_dec(v_etaArgs_113_);
lean_del_object(v___x_111_);
lean_dec(v_snd_109_);
lean_dec(v_fst_108_);
lean_dec(v_fst_107_);
lean_dec(v_fst_106_);
return v___x_102_;
}
}
}
else
{
lean_dec(v_snd_105_);
lean_dec(v_snd_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_kind_101_);
return v___x_102_;
}
}
else
{
lean_dec_ref(v_kind_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___boxed(lean_object* v_specThm_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate(v_specThm_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_251_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_252_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0(lean_object* v_00_u03b2_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0(lean_box(0));
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1);
v___x_260_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default;
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v_env_271_; lean_object* v___x_272_; lean_object* v_mctx_273_; lean_object* v_lctx_274_; lean_object* v_options_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_270_ = lean_st_ref_get(v___y_268_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_env_271_);
lean_dec(v___x_270_);
v___x_272_ = lean_st_ref_get(v___y_266_);
v_mctx_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_mctx_273_);
lean_dec(v___x_272_);
v_lctx_274_ = lean_ctor_get(v___y_265_, 2);
v_options_275_ = lean_ctor_get(v___y_267_, 2);
lean_inc_ref(v_options_275_);
lean_inc_ref(v_lctx_274_);
v___x_276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_276_, 0, v_env_271_);
lean_ctor_set(v___x_276_, 1, v_mctx_273_);
lean_ctor_set(v___x_276_, 2, v_lctx_274_);
lean_ctor_set(v___x_276_, 3, v_options_275_);
v___x_277_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_msgData_264_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0___boxed(lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msgData_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(lean_object* v_msg_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_ref_292_; lean_object* v___x_293_; lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_302_; 
v_ref_292_ = lean_ctor_get(v___y_289_, 5);
v___x_293_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_302_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_inc(v_ref_292_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_ref_292_);
lean_ctor_set(v___x_298_, 1, v_a_294_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 1);
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg___boxed(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_309_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0(lean_object* v_type_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
lean_inc_ref(v_type_320_);
v___x_331_ = l_Lean_Expr_cleanupAnnotations(v_type_320_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_331_);
goto v___jp_326_;
}
else
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_334_ = l_Lean_Expr_isApp(v___x_333_);
if (v___x_334_ == 0)
{
lean_dec_ref(v___x_333_);
goto v___jp_326_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_333_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_335_);
goto v___jp_326_;
}
else
{
lean_object* v_arg_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_arg_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc_ref(v_arg_337_);
v___x_338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_339_ = l_Lean_Expr_isApp(v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v___x_338_);
lean_dec_ref(v_arg_337_);
goto v___jp_326_;
}
else
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_338_);
v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_337_);
goto v___jp_326_;
}
else
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
lean_dec_ref(v_arg_337_);
goto v___jp_326_;
}
else
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_345_ = l_Lean_Expr_isApp(v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v___x_344_);
lean_dec_ref(v_arg_337_);
goto v___jp_326_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_344_);
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_346_, v___x_347_);
lean_dec_ref(v___x_346_);
if (v___x_348_ == 0)
{
lean_dec_ref(v_arg_337_);
goto v___jp_326_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec_ref(v_type_320_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v_arg_337_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
}
}
}
}
}
v___jp_326_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1);
v___x_328_ = l_Lean_indentExpr(v_type_320_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v___x_329_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___boxed(lean_object* v_type_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0(v_type_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(lean_object* v_expr_362_, lean_object* v_levelParams_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(v_expr_362_, v_levelParams_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v_fst_371_; lean_object* v_snd_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_369_);
v_fst_371_ = lean_ctor_get(v_a_370_, 0);
lean_inc(v_fst_371_);
v_snd_372_ = lean_ctor_get(v_a_370_, 1);
lean_inc_n(v_snd_372_, 2);
lean_dec(v_a_370_);
v___f_373_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0));
v___x_374_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1));
v___x_375_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_box(0), v_fst_371_, v_snd_372_, v___f_373_, v_snd_372_, v___x_374_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_fst_380_; lean_object* v___x_382_; 
v_fst_380_ = lean_ctor_get(v_a_376_, 0);
lean_inc(v_fst_380_);
lean_dec(v_a_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v_fst_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_fst_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_375_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_369_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_369_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___boxed(lean_object* v_expr_401_, lean_object* v_levelParams_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(v_expr_401_, v_levelParams_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr(lean_object* v_expr_409_, lean_object* v_levelParams_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(v_expr_409_, v_levelParams_410_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___boxed(lean_object* v_expr_419_, lean_object* v_levelParams_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr(v_expr_419_, v_levelParams_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0(lean_object* v_00_u03b1_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___boxed(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0(v_00_u03b1_437_, v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(lean_object* v_e_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_Expr_hasMVar(v_e_445_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_e_445_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v_mctx_451_; lean_object* v___x_452_; lean_object* v_fst_453_; lean_object* v_snd_454_; lean_object* v___x_455_; lean_object* v_cache_456_; lean_object* v_zetaDeltaFVarIds_457_; lean_object* v_postponed_458_; lean_object* v_diag_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v___x_450_ = lean_st_ref_get(v___y_446_);
v_mctx_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_mctx_451_);
lean_dec(v___x_450_);
v___x_452_ = l_Lean_instantiateMVarsCore(v_mctx_451_, v_e_445_);
v_fst_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_fst_453_);
v_snd_454_ = lean_ctor_get(v___x_452_, 1);
lean_inc(v_snd_454_);
lean_dec_ref(v___x_452_);
v___x_455_ = lean_st_ref_take(v___y_446_);
v_cache_456_ = lean_ctor_get(v___x_455_, 1);
v_zetaDeltaFVarIds_457_ = lean_ctor_get(v___x_455_, 2);
v_postponed_458_ = lean_ctor_get(v___x_455_, 3);
v_diag_459_ = lean_ctor_get(v___x_455_, 4);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_455_, 0);
lean_dec(v_unused_469_);
v___x_461_ = v___x_455_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_diag_459_);
lean_inc(v_postponed_458_);
lean_inc(v_zetaDeltaFVarIds_457_);
lean_inc(v_cache_456_);
lean_dec(v___x_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v_snd_454_);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_snd_454_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_cache_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_zetaDeltaFVarIds_457_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_postponed_458_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_diag_459_);
v___x_464_ = v_reuseFailAlloc_467_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_st_ref_set(v___y_446_, v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_fst_453_);
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg___boxed(lean_object* v_e_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_470_, v___y_471_);
lean_dec(v___y_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0(lean_object* v_e_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_474_, v___y_478_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___boxed(lean_object* v_e_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0(v_e_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0(lean_object* v_k_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
v___x_500_ = lean_apply_7(v_k_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, lean_box(0));
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0___boxed(lean_object* v_k_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0(v_k_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(lean_object* v_k_510_, uint8_t v_allowLevelAssignments_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___f_519_; lean_object* v___x_520_; 
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
v___f_519_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_519_, 0, v_k_510_);
lean_closure_set(v___f_519_, 1, v___y_512_);
lean_closure_set(v___f_519_, 2, v___y_513_);
v___x_520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_511_, v___f_519_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
return v___x_520_;
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___boxed(lean_object* v_k_529_, lean_object* v_allowLevelAssignments_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_538_; lean_object* v_res_539_; 
v_allowLevelAssignments_boxed_538_ = lean_unbox(v_allowLevelAssignments_530_);
v_res_539_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v_k_529_, v_allowLevelAssignments_boxed_538_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2(lean_object* v_00_u03b1_540_, lean_object* v_k_541_, uint8_t v_allowLevelAssignments_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v_k_541_, v_allowLevelAssignments_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___boxed(lean_object* v_00_u03b1_551_, lean_object* v_k_552_, lean_object* v_allowLevelAssignments_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_561_; lean_object* v_res_562_; 
v_allowLevelAssignments_boxed_561_ = lean_unbox(v_allowLevelAssignments_553_);
v_res_562_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2(v_00_u03b1_551_, v_k_552_, v_allowLevelAssignments_boxed_561_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_ref_569_; lean_object* v___x_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_ref_569_ = lean_ctor_get(v___y_566_, 5);
v___x_570_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_ref_569_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_ref_569_);
lean_ctor_set(v___x_575_, 1, v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 1);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg___boxed(lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(lean_object* v_a_597_, lean_object* v___x_598_, uint8_t v___x_599_, lean_object* v___x_600_, lean_object* v_a_601_, lean_object* v_proof_602_, lean_object* v_prio_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; lean_object* v_config_612_; uint8_t v_trackZetaDelta_613_; lean_object* v_zetaDeltaSet_614_; lean_object* v_lctx_615_; lean_object* v_localInstances_616_; lean_object* v_defEqCtx_x3f_617_; lean_object* v_synthPendingDepth_618_; lean_object* v_canUnfold_x3f_619_; uint8_t v_univApprox_620_; uint8_t v_inTypeClassResolution_621_; uint8_t v_cacheInferType_622_; uint64_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_611_ = l_Lean_Meta_simpGlobalConfig;
v_config_612_ = lean_ctor_get(v___x_611_, 0);
v_trackZetaDelta_613_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*7);
v_zetaDeltaSet_614_ = lean_ctor_get(v___y_606_, 1);
v_lctx_615_ = lean_ctor_get(v___y_606_, 2);
v_localInstances_616_ = lean_ctor_get(v___y_606_, 3);
v_defEqCtx_x3f_617_ = lean_ctor_get(v___y_606_, 4);
v_synthPendingDepth_618_ = lean_ctor_get(v___y_606_, 5);
v_canUnfold_x3f_619_ = lean_ctor_get(v___y_606_, 6);
v_univApprox_620_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_621_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*7 + 2);
v_cacheInferType_622_ = lean_ctor_get_uint8(v___y_606_, sizeof(void*)*7 + 3);
v___x_623_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_612_);
lean_inc_ref(v_config_612_);
v___x_624_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_624_, 0, v_config_612_);
lean_ctor_set_uint64(v___x_624_, sizeof(void*)*1, v___x_623_);
lean_inc(v_canUnfold_x3f_619_);
lean_inc(v_synthPendingDepth_618_);
lean_inc(v_defEqCtx_x3f_617_);
lean_inc_ref(v_localInstances_616_);
lean_inc_ref(v_lctx_615_);
lean_inc(v_zetaDeltaSet_614_);
v___x_625_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v_zetaDeltaSet_614_);
lean_ctor_set(v___x_625_, 2, v_lctx_615_);
lean_ctor_set(v___x_625_, 3, v_localInstances_616_);
lean_ctor_set(v___x_625_, 4, v_defEqCtx_x3f_617_);
lean_ctor_set(v___x_625_, 5, v_synthPendingDepth_618_);
lean_ctor_set(v___x_625_, 6, v_canUnfold_x3f_619_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*7, v_trackZetaDelta_613_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*7 + 1, v_univApprox_620_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*7 + 2, v_inTypeClassResolution_621_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*7 + 3, v_cacheInferType_622_);
v___x_626_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_597_, v___x_598_, v___x_599_, v___x_625_, v___y_607_, v___y_608_, v___y_609_);
lean_dec_ref(v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_snd_628_; lean_object* v_fst_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_710_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref(v___x_626_);
v_snd_628_ = lean_ctor_get(v_a_627_, 1);
v_fst_629_ = lean_ctor_get(v_a_627_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_627_);
if (v_isSharedCheck_710_ == 0)
{
v___x_631_ = v_a_627_;
v_isShared_632_ = v_isSharedCheck_710_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_628_);
lean_inc(v_fst_629_);
lean_dec(v_a_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_710_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_708_; 
v_snd_633_ = lean_ctor_get(v_snd_628_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_snd_628_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_snd_628_, 0);
lean_dec(v_unused_709_);
v___x_635_ = v_snd_628_;
v_isShared_636_ = v_isSharedCheck_708_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_dec(v_snd_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_708_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Meta_whnfR(v_snd_633_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_n(v_a_638_, 2);
lean_dec_ref(v___x_637_);
v___x_652_ = l_Lean_Expr_cleanupAnnotations(v_a_638_);
v___x_653_ = l_Lean_Expr_isApp(v___x_652_);
if (v___x_653_ == 0)
{
lean_dec_ref(v___x_652_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_652_);
v___x_655_ = l_Lean_Expr_isApp(v___x_654_);
if (v___x_655_ == 0)
{
lean_dec_ref(v___x_654_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v_arg_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_arg_656_ = lean_ctor_get(v___x_654_, 1);
lean_inc_ref(v_arg_656_);
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_654_);
v___x_658_ = l_Lean_Expr_isApp(v___x_657_);
if (v___x_658_ == 0)
{
lean_dec_ref(v___x_657_);
lean_dec_ref(v_arg_656_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_657_);
v___x_660_ = l_Lean_Expr_isApp(v___x_659_);
if (v___x_660_ == 0)
{
lean_dec_ref(v___x_659_);
lean_dec_ref(v_arg_656_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_659_);
v___x_662_ = l_Lean_Expr_isApp(v___x_661_);
if (v___x_662_ == 0)
{
lean_dec_ref(v___x_661_);
lean_dec_ref(v_arg_656_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_661_);
v___x_664_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_664_ == 0)
{
lean_dec_ref(v___x_663_);
lean_dec_ref(v_arg_656_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v_arg_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_arg_665_ = lean_ctor_get(v___x_663_, 1);
lean_inc_ref(v_arg_665_);
v___x_666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
v___x_667_ = l_Lean_Expr_isApp(v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v___x_666_);
lean_dec_ref(v_arg_665_);
lean_dec_ref(v_arg_656_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_666_);
v___x_669_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5));
v___x_670_ = l_Lean_Expr_isConstOf(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec_ref(v___x_668_);
lean_dec_ref(v_arg_665_);
lean_dec_ref(v_arg_656_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
v___y_642_ = v___y_606_;
v___y_643_ = v___y_607_;
v___y_644_ = v___y_608_;
v___y_645_ = v___y_609_;
goto v___jp_639_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_dec(v_a_638_);
lean_del_object(v___x_635_);
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__4));
v___x_672_ = l_Lean_Expr_constLevels_x21(v___x_668_);
lean_dec_ref(v___x_668_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_List_get_x21Internal___redArg(v___x_600_, v___x_672_, v___x_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 1);
lean_ctor_set(v___x_631_, 1, v___x_675_);
lean_ctor_set(v___x_631_, 0, v___x_674_);
v___x_677_ = v___x_631_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_699_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_mkConst(v___x_671_, v___x_677_);
v___x_679_ = l_Lean_Expr_app___override(v___x_678_, v_arg_665_);
v___x_680_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_629_, v___x_679_, v_arg_656_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_690_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_690_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_690_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_690_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_a_681_);
v___x_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_686_, 0, v_a_601_);
lean_ctor_set(v___x_686_, 1, v_proof_602_);
lean_ctor_set(v___x_686_, 2, v___x_685_);
lean_ctor_set(v___x_686_, 3, v_prio_603_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_686_);
v___x_688_ = v___x_683_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v_a_691_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_680_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_680_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
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
v___jp_639_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1);
v___x_647_ = l_Lean_indentExpr(v_a_638_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 7);
lean_ctor_set(v___x_635_, 1, v___x_647_);
lean_ctor_set(v___x_635_, 0, v___x_646_);
v___x_649_ = v___x_635_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_651_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_649_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_650_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_635_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v_a_700_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_637_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_637_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_prio_603_);
lean_dec_ref(v_proof_602_);
lean_dec_ref(v_a_601_);
v_a_711_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_626_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_626_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed(lean_object* v_a_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_a_723_, lean_object* v_proof_724_, lean_object* v_prio_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v___x_17701__boxed_733_; lean_object* v_res_734_; 
v___x_17701__boxed_733_ = lean_unbox(v___x_721_);
v_res_734_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(v_a_719_, v___x_720_, v___x_17701__boxed_733_, v___x_722_, v_a_723_, v_proof_724_, v_prio_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___x_722_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__0));
v___x_737_ = l_Lean_stringToMessageData(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(lean_object* v_proof_738_, lean_object* v_prio_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; 
lean_inc_ref(v_proof_738_);
v___x_747_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(v_proof_738_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_815_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
v_fst_749_ = lean_ctor_get(v_a_748_, 0);
v_snd_750_ = lean_ctor_get(v_a_748_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_815_ == 0)
{
v___x_752_ = v_a_748_;
v_isShared_753_ = v_isSharedCheck_815_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_inc(v_fst_749_);
lean_dec(v_a_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_815_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; 
lean_inc(v_a_745_);
lean_inc_ref(v_a_744_);
lean_inc(v_a_743_);
lean_inc_ref(v_a_742_);
lean_inc(v_snd_750_);
v___x_754_ = lean_infer_type(v_snd_750_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref(v___x_754_);
v___x_756_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_a_755_, v_a_743_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc_n(v_a_757_, 2);
lean_dec_ref(v___x_756_);
v___x_758_ = l_Lean_Meta_isProp(v_a_757_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___x_784_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = lean_box(0);
v___x_784_ = lean_unbox(v_a_759_);
lean_dec(v_a_759_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
lean_dec(v_snd_750_);
lean_dec(v_fst_749_);
lean_dec(v_prio_739_);
lean_dec_ref(v_proof_738_);
v___x_785_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___closed__1);
v___x_786_ = l_Lean_indentExpr(v_a_757_);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 7);
lean_ctor_set(v___x_752_, 1, v___x_786_);
lean_ctor_set(v___x_752_, 0, v___x_785_);
v___x_788_ = v___x_752_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_798_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v___x_789_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_788_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
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
else
{
lean_del_object(v___x_752_);
v___y_762_ = v_a_740_;
v___y_763_ = v_a_741_;
v___y_764_ = v_a_742_;
v___y_765_ = v_a_743_;
v___y_766_ = v_a_744_;
v___y_767_ = v_a_745_;
goto v___jp_761_;
}
v___jp_761_:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(v_snd_750_, v_fst_749_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___f_773_; uint8_t v___x_774_; lean_object* v___x_775_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v___x_770_ = lean_box(0);
v___x_771_ = 0;
v___x_772_ = lean_box(v___x_771_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed), 14, 7);
lean_closure_set(v___f_773_, 0, v_a_757_);
lean_closure_set(v___f_773_, 1, v___x_770_);
lean_closure_set(v___f_773_, 2, v___x_772_);
lean_closure_set(v___f_773_, 3, v___x_760_);
lean_closure_set(v___f_773_, 4, v_a_769_);
lean_closure_set(v___f_773_, 5, v_proof_738_);
lean_closure_set(v___f_773_, 6, v_prio_739_);
v___x_774_ = 0;
v___x_775_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v___f_773_, v___x_774_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_775_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_757_);
lean_dec(v_prio_739_);
lean_dec_ref(v_proof_738_);
v_a_776_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_768_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_768_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_757_);
lean_del_object(v___x_752_);
lean_dec(v_snd_750_);
lean_dec(v_fst_749_);
lean_dec(v_prio_739_);
lean_dec_ref(v_proof_738_);
v_a_799_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_758_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_758_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
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
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_del_object(v___x_752_);
lean_dec(v_snd_750_);
lean_dec(v_fst_749_);
lean_dec(v_prio_739_);
lean_dec_ref(v_proof_738_);
v_a_807_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_754_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_754_);
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
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_prio_739_);
lean_dec_ref(v_proof_738_);
v_a_816_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_747_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_747_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___boxed(lean_object* v_proof_824_, lean_object* v_prio_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(v_proof_824_, v_prio_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(lean_object* v_00_u03b1_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v_msg_835_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___boxed(lean_object* v_00_u03b1_844_, lean_object* v_msg_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(v_00_u03b1_844_, v_msg_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(lean_object* v_ty_854_, lean_object* v_acc_855_){
_start:
{
if (lean_obj_tag(v_ty_854_) == 7)
{
lean_object* v_binderType_856_; lean_object* v_body_857_; lean_object* v___x_858_; 
v_binderType_856_ = lean_ctor_get(v_ty_854_, 1);
lean_inc_ref(v_binderType_856_);
v_body_857_ = lean_ctor_get(v_ty_854_, 2);
lean_inc_ref(v_body_857_);
lean_dec_ref(v_ty_854_);
v___x_858_ = lean_array_push(v_acc_855_, v_binderType_856_);
v_ty_854_ = v_body_857_;
v_acc_855_ = v___x_858_;
goto _start;
}
else
{
lean_dec_ref(v_ty_854_);
return v_acc_855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(lean_object* v_k_860_, lean_object* v_i_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_sub(v_k_860_, v___x_862_);
v___x_864_ = lean_nat_sub(v___x_863_, v_i_861_);
lean_dec(v___x_863_);
v___x_865_ = l_Lean_mkBVar(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed(lean_object* v_k_866_, lean_object* v_i_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(v_k_866_, v_i_867_);
lean_dec(v_i_867_);
lean_dec(v_k_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(lean_object* v_pattern_869_, lean_object* v_eqTy_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_Expr_isForall(v_eqTy_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_eqTy_870_);
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_pattern_869_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v_levelParams_874_; lean_object* v_varTypes_875_; lean_object* v_pattern_876_; lean_object* v_fnInfos_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_895_; 
v_levelParams_874_ = lean_ctor_get(v_pattern_869_, 0);
v_varTypes_875_ = lean_ctor_get(v_pattern_869_, 1);
v_pattern_876_ = lean_ctor_get(v_pattern_869_, 3);
v_fnInfos_877_ = lean_ctor_get(v_pattern_869_, 4);
v_isSharedCheck_895_ = !lean_is_exclusive(v_pattern_869_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; lean_object* v_unused_897_; 
v_unused_896_ = lean_ctor_get(v_pattern_869_, 5);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_pattern_869_, 2);
lean_dec(v_unused_897_);
v___x_879_ = v_pattern_869_;
v_isShared_880_ = v_isSharedCheck_895_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_fnInfos_877_);
lean_inc(v_pattern_876_);
lean_inc(v_varTypes_875_);
lean_inc(v_levelParams_874_);
lean_dec(v_pattern_869_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_895_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_extraDomains_883_; lean_object* v_k_884_; lean_object* v___f_885_; lean_object* v_liftedPattern_886_; lean_object* v_newBVars_887_; lean_object* v_newPatternExpr_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_newPattern_892_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1));
v_extraDomains_883_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(v_eqTy_870_, v___x_882_);
v_k_884_ = lean_array_get_size(v_extraDomains_883_);
v___f_885_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed), 2, 1);
lean_closure_set(v___f_885_, 0, v_k_884_);
v_liftedPattern_886_ = lean_expr_lift_loose_bvars(v_pattern_876_, v___x_881_, v_k_884_);
lean_dec_ref(v_pattern_876_);
v_newBVars_887_ = l_Array_ofFn___redArg(v_k_884_, v___f_885_);
v_newPatternExpr_888_ = l_Lean_mkAppN(v_liftedPattern_886_, v_newBVars_887_);
lean_dec_ref(v_newBVars_887_);
v___x_889_ = l_Array_append___redArg(v_varTypes_875_, v_extraDomains_883_);
lean_dec_ref(v_extraDomains_883_);
v___x_890_ = lean_box(0);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 5, v___x_890_);
lean_ctor_set(v___x_879_, 3, v_newPatternExpr_888_);
lean_ctor_set(v___x_879_, 2, v___x_890_);
lean_ctor_set(v___x_879_, 1, v___x_889_);
v_newPattern_892_ = v___x_879_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_levelParams_874_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_newPatternExpr_888_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_fnInfos_877_);
lean_ctor_set(v_reuseFailAlloc_894_, 5, v___x_890_);
v_newPattern_892_ = v_reuseFailAlloc_894_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_newPattern_892_);
lean_ctor_set(v___x_893_, 1, v_k_884_);
return v___x_893_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(lean_object* v_body_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
lean_inc_ref(v_body_901_);
v___x_912_ = l_Lean_Expr_cleanupAnnotations(v_body_901_);
v___x_913_ = l_Lean_Expr_isApp(v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v___x_912_);
goto v___jp_907_;
}
else
{
lean_object* v_arg_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_arg_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc_ref(v_arg_914_);
v___x_915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_912_);
v___x_916_ = l_Lean_Expr_isApp(v___x_915_);
if (v___x_916_ == 0)
{
lean_dec_ref(v___x_915_);
lean_dec_ref(v_arg_914_);
goto v___jp_907_;
}
else
{
lean_object* v_arg_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_arg_917_ = lean_ctor_get(v___x_915_, 1);
lean_inc_ref(v_arg_917_);
v___x_918_ = l_Lean_Expr_appFnCleanup___redArg(v___x_915_);
v___x_919_ = l_Lean_Expr_isApp(v___x_918_);
if (v___x_919_ == 0)
{
lean_dec_ref(v___x_918_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
goto v___jp_907_;
}
else
{
lean_object* v_arg_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_arg_920_ = lean_ctor_get(v___x_918_, 1);
lean_inc_ref(v_arg_920_);
v___x_921_ = l_Lean_Expr_appFnCleanup___redArg(v___x_918_);
v___x_922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1));
v___x_923_ = l_Lean_Expr_isConstOf(v___x_921_, v___x_922_);
lean_dec_ref(v___x_921_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
goto v___jp_907_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_body_901_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_arg_920_);
lean_ctor_set(v___x_924_, 1, v_arg_914_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_arg_917_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
}
v___jp_907_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1);
v___x_909_ = l_Lean_indentExpr(v_body_901_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v___x_910_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___boxed(lean_object* v_body_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(v_body_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(lean_object* v_declName_935_, lean_object* v_prio_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; 
lean_inc(v_declName_935_);
v___x_942_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern(v_declName_935_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref(v___x_942_);
v_fst_944_ = lean_ctor_get(v_a_943_, 0);
lean_inc(v_fst_944_);
v_snd_945_ = lean_ctor_get(v_a_943_, 1);
lean_inc_n(v_snd_945_, 2);
lean_dec(v_a_943_);
v___f_946_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0));
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1));
v___x_949_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_box(0), v_fst_944_, v_snd_945_, v___f_946_, v_snd_945_, v___x_948_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_977_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_977_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_977_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_977_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_snd_954_; lean_object* v_fst_955_; lean_object* v_fst_956_; lean_object* v_snd_957_; lean_object* v___x_958_; lean_object* v_fst_959_; lean_object* v_snd_960_; uint8_t v___y_962_; uint8_t v___x_974_; 
v_snd_954_ = lean_ctor_get(v_a_950_, 1);
lean_inc(v_snd_954_);
v_fst_955_ = lean_ctor_get(v_a_950_, 0);
lean_inc(v_fst_955_);
lean_dec(v_a_950_);
v_fst_956_ = lean_ctor_get(v_snd_954_, 0);
lean_inc(v_fst_956_);
v_snd_957_ = lean_ctor_get(v_snd_954_, 1);
lean_inc(v_snd_957_);
lean_dec(v_snd_954_);
v___x_958_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(v_fst_955_, v_fst_956_);
v_fst_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_fst_959_);
v_snd_960_ = lean_ctor_get(v___x_958_, 1);
lean_inc(v_snd_960_);
lean_dec_ref(v___x_958_);
v___x_974_ = lean_nat_dec_eq(v_snd_960_, v___x_947_);
if (v___x_974_ == 0)
{
lean_dec(v_snd_957_);
v___y_962_ = v___x_974_;
goto v___jp_961_;
}
else
{
lean_object* v_pattern_975_; uint8_t v___x_976_; 
v_pattern_975_ = lean_ctor_get(v_fst_959_, 3);
v___x_976_ = lean_expr_eqv(v_pattern_975_, v_snd_957_);
lean_dec(v_snd_957_);
v___y_962_ = v___x_976_;
goto v___jp_961_;
}
v___jp_961_:
{
if (v___y_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_declName_935_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v_snd_960_);
v___x_965_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_965_, 0, v_fst_959_);
lean_ctor_set(v___x_965_, 1, v___x_963_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
lean_ctor_set(v___x_965_, 3, v_prio_936_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_966_);
v___x_968_ = v___x_952_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_snd_960_);
lean_dec(v_fst_959_);
lean_dec(v_prio_936_);
lean_dec(v_declName_935_);
v___x_970_ = lean_box(0);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_970_);
v___x_972_ = v___x_952_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_prio_936_);
lean_dec(v_declName_935_);
v_a_978_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_949_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_949_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_prio_936_);
lean_dec(v_declName_935_);
v_a_986_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_942_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_942_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___boxed(lean_object* v_declName_994_, lean_object* v_prio_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_declName_994_, v_prio_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__0(lean_object* v_x1_1002_, lean_object* v_x2_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_array_push(v_x1_1002_, v_x2_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(lean_object* v_f_1005_, lean_object* v_as_1006_, size_t v_i_1007_, size_t v_stop_1008_, lean_object* v_b_1009_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_usize_dec_eq(v_i_1007_, v_stop_1008_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; 
v___x_1011_ = lean_array_uget_borrowed(v_as_1006_, v_i_1007_);
lean_inc(v_f_1005_);
lean_inc(v___x_1011_);
v___x_1012_ = lean_apply_2(v_f_1005_, v_b_1009_, v___x_1011_);
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_add(v_i_1007_, v___x_1013_);
v_i_1007_ = v___x_1014_;
v_b_1009_ = v___x_1012_;
goto _start;
}
else
{
lean_dec(v_f_1005_);
return v_b_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg___boxed(lean_object* v_f_1016_, lean_object* v_as_1017_, lean_object* v_i_1018_, lean_object* v_stop_1019_, lean_object* v_b_1020_){
_start:
{
size_t v_i_boxed_1021_; size_t v_stop_boxed_1022_; lean_object* v_res_1023_; 
v_i_boxed_1021_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_stop_boxed_1022_ = lean_unbox_usize(v_stop_1019_);
lean_dec(v_stop_1019_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_1016_, v_as_1017_, v_i_boxed_1021_, v_stop_boxed_1022_, v_b_1020_);
lean_dec_ref(v_as_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(lean_object* v_f_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_vs_1027_; lean_object* v_children_1028_; lean_object* v___x_1029_; lean_object* v_s_1031_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_vs_1027_ = lean_ctor_get(v_x_1026_, 0);
v_children_1028_ = lean_ctor_get(v_x_1026_, 1);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_array_get_size(v_vs_1027_);
v___x_1042_ = lean_nat_dec_lt(v___x_1029_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_array_get_size(v_children_1028_);
v___x_1044_ = lean_nat_dec_lt(v___x_1029_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec(v_f_1024_);
return v_x_1025_;
}
else
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_nat_dec_le(v___x_1043_, v___x_1043_);
if (v___x_1045_ == 0)
{
if (v___x_1044_ == 0)
{
lean_dec(v_f_1024_);
return v_x_1025_;
}
else
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = lean_usize_of_nat(v___x_1043_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_1024_, v_children_1028_, v___x_1046_, v___x_1047_, v_x_1025_);
return v___x_1048_;
}
}
else
{
size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = lean_usize_of_nat(v___x_1043_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_1024_, v_children_1028_, v___x_1049_, v___x_1050_, v_x_1025_);
return v___x_1051_;
}
}
}
else
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_nat_dec_le(v___x_1041_, v___x_1041_);
if (v___x_1052_ == 0)
{
if (v___x_1042_ == 0)
{
v_s_1031_ = v_x_1025_;
goto v___jp_1030_;
}
else
{
size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v_f_1024_);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_1024_, v_vs_1027_, v___x_1053_, v___x_1054_, v_x_1025_);
v_s_1031_ = v___x_1055_;
goto v___jp_1030_;
}
}
else
{
size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = ((size_t)0ULL);
v___x_1057_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v_f_1024_);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_1024_, v_vs_1027_, v___x_1056_, v___x_1057_, v_x_1025_);
v_s_1031_ = v___x_1058_;
goto v___jp_1030_;
}
}
v___jp_1030_:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_array_get_size(v_children_1028_);
v___x_1033_ = lean_nat_dec_lt(v___x_1029_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_dec(v_f_1024_);
return v_s_1031_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1032_);
if (v___x_1034_ == 0)
{
if (v___x_1033_ == 0)
{
lean_dec(v_f_1024_);
return v_s_1031_;
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1032_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_1024_, v_children_1028_, v___x_1035_, v___x_1036_, v_s_1031_);
return v___x_1037_;
}
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = lean_usize_of_nat(v___x_1032_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_1024_, v_children_1028_, v___x_1038_, v___x_1039_, v_s_1031_);
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(lean_object* v_f_1059_, lean_object* v_as_1060_, size_t v_i_1061_, size_t v_stop_1062_, lean_object* v_b_1063_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_eq(v_i_1061_, v_stop_1062_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v_snd_1066_; lean_object* v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; 
v___x_1065_ = lean_array_uget_borrowed(v_as_1060_, v_i_1061_);
v_snd_1066_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_f_1059_);
v___x_1067_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_1059_, v_b_1063_, v_snd_1066_);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1061_, v___x_1068_);
v_i_1061_ = v___x_1069_;
v_b_1063_ = v___x_1067_;
goto _start;
}
else
{
lean_dec(v_f_1059_);
return v_b_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg___boxed(lean_object* v_f_1071_, lean_object* v_as_1072_, lean_object* v_i_1073_, lean_object* v_stop_1074_, lean_object* v_b_1075_){
_start:
{
size_t v_i_boxed_1076_; size_t v_stop_boxed_1077_; lean_object* v_res_1078_; 
v_i_boxed_1076_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_stop_boxed_1077_ = lean_unbox_usize(v_stop_1074_);
lean_dec(v_stop_1074_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_1071_, v_as_1072_, v_i_boxed_1076_, v_stop_boxed_1077_, v_b_1075_);
lean_dec_ref(v_as_1072_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg___boxed(lean_object* v_f_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_1079_, v_x_1080_, v_x_1081_);
lean_dec_ref(v_x_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(lean_object* v___f_1083_, lean_object* v_s_1084_, lean_object* v_x_1085_, lean_object* v_t_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v___f_1083_, v_s_1084_, v_t_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1___boxed(lean_object* v___f_1088_, lean_object* v_s_1089_, lean_object* v_x_1090_, lean_object* v_t_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(v___f_1088_, v_s_1089_, v_x_1090_, v_t_1091_);
lean_dec_ref(v_t_1091_);
lean_dec(v_x_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__2(lean_object* v_x1_1093_, lean_object* v_x2_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_array_push(v_x1_1093_, v_x2_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(lean_object* v___f_1096_, lean_object* v_s_1097_, lean_object* v_x_1098_, lean_object* v_t_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v___f_1096_, v_s_1097_, v_t_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3___boxed(lean_object* v___f_1101_, lean_object* v_s_1102_, lean_object* v_x_1103_, lean_object* v_t_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(v___f_1101_, v_s_1102_, v_x_1103_, v_t_1104_);
lean_dec_ref(v_t_1104_);
lean_dec(v_x_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg(lean_object* v_keys_1106_, lean_object* v_i_1107_, lean_object* v_k_1108_){
_start:
{
uint8_t v___y_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_array_get_size(v_keys_1106_);
v___x_1116_ = lean_nat_dec_lt(v_i_1107_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec(v_i_1107_);
return v___x_1116_;
}
else
{
lean_object* v_k_x27_1117_; 
v_k_x27_1117_ = lean_array_fget_borrowed(v_keys_1106_, v_i_1107_);
if (lean_obj_tag(v_k_1108_) == 0)
{
if (lean_obj_tag(v_k_x27_1117_) == 0)
{
lean_object* v_declName_1118_; uint8_t v_inv_1119_; lean_object* v_declName_1120_; uint8_t v_inv_1121_; uint8_t v___x_1122_; 
v_declName_1118_ = lean_ctor_get(v_k_1108_, 0);
v_inv_1119_ = lean_ctor_get_uint8(v_k_1108_, sizeof(void*)*1 + 1);
v_declName_1120_ = lean_ctor_get(v_k_x27_1117_, 0);
v_inv_1121_ = lean_ctor_get_uint8(v_k_x27_1117_, sizeof(void*)*1 + 1);
v___x_1122_ = lean_name_eq(v_declName_1118_, v_declName_1120_);
if (v___x_1122_ == 0)
{
v___y_1114_ = v___x_1122_;
goto v___jp_1113_;
}
else
{
if (v_inv_1119_ == 0)
{
if (v_inv_1121_ == 0)
{
v___y_1114_ = v___x_1122_;
goto v___jp_1113_;
}
else
{
goto v___jp_1109_;
}
}
else
{
v___y_1114_ = v_inv_1121_;
goto v___jp_1113_;
}
}
}
else
{
goto v___jp_1109_;
}
}
else
{
if (lean_obj_tag(v_k_x27_1117_) == 0)
{
goto v___jp_1109_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = l_Lean_Meta_Origin_key(v_k_1108_);
v___x_1124_ = l_Lean_Meta_Origin_key(v_k_x27_1117_);
v___x_1125_ = lean_name_eq(v___x_1123_, v___x_1124_);
lean_dec(v___x_1124_);
lean_dec(v___x_1123_);
v___y_1114_ = v___x_1125_;
goto v___jp_1113_;
}
}
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_unsigned_to_nat(1u);
v___x_1111_ = lean_nat_add(v_i_1107_, v___x_1110_);
lean_dec(v_i_1107_);
v_i_1107_ = v___x_1111_;
goto _start;
}
v___jp_1113_:
{
if (v___y_1114_ == 0)
{
goto v___jp_1109_;
}
else
{
lean_dec(v_i_1107_);
return v___y_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_keys_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg(v_keys_1126_, v_i_1127_, v_k_1128_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_keys_1126_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; 
v___x_1131_ = ((size_t)5ULL);
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_shift_left(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; 
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__0);
v___x_1136_ = lean_usize_sub(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(lean_object* v_x_1137_, size_t v_x_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
lean_object* v_es_1140_; lean_object* v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; lean_object* v_j_1145_; lean_object* v___x_1146_; 
v_es_1140_ = lean_ctor_get(v_x_1137_, 0);
v___x_1141_ = lean_box(2);
v___x_1142_ = ((size_t)5ULL);
v___x_1143_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1);
v___x_1144_ = lean_usize_land(v_x_1138_, v___x_1143_);
v_j_1145_ = lean_usize_to_nat(v___x_1144_);
v___x_1146_ = lean_array_get_borrowed(v___x_1141_, v_es_1140_, v_j_1145_);
lean_dec(v_j_1145_);
switch(lean_obj_tag(v___x_1146_))
{
case 0:
{
if (lean_obj_tag(v_x_1139_) == 0)
{
lean_object* v_key_1147_; 
v_key_1147_ = lean_ctor_get(v___x_1146_, 0);
if (lean_obj_tag(v_key_1147_) == 0)
{
lean_object* v_declName_1148_; uint8_t v_inv_1149_; lean_object* v_declName_1150_; uint8_t v_inv_1151_; uint8_t v___x_1152_; 
v_declName_1148_ = lean_ctor_get(v_x_1139_, 0);
v_inv_1149_ = lean_ctor_get_uint8(v_x_1139_, sizeof(void*)*1 + 1);
v_declName_1150_ = lean_ctor_get(v_key_1147_, 0);
v_inv_1151_ = lean_ctor_get_uint8(v_key_1147_, sizeof(void*)*1 + 1);
v___x_1152_ = lean_name_eq(v_declName_1148_, v_declName_1150_);
if (v___x_1152_ == 0)
{
return v___x_1152_;
}
else
{
if (v_inv_1149_ == 0)
{
if (v_inv_1151_ == 0)
{
return v___x_1152_;
}
else
{
return v_inv_1149_;
}
}
else
{
return v_inv_1151_;
}
}
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
return v___x_1153_;
}
}
else
{
lean_object* v_key_1154_; 
v_key_1154_ = lean_ctor_get(v___x_1146_, 0);
if (lean_obj_tag(v_key_1154_) == 0)
{
uint8_t v___x_1155_; 
v___x_1155_ = 0;
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = l_Lean_Meta_Origin_key(v_x_1139_);
v___x_1157_ = l_Lean_Meta_Origin_key(v_key_1154_);
v___x_1158_ = lean_name_eq(v___x_1156_, v___x_1157_);
lean_dec(v___x_1157_);
lean_dec(v___x_1156_);
return v___x_1158_;
}
}
}
case 1:
{
lean_object* v_node_1159_; size_t v___x_1160_; 
v_node_1159_ = lean_ctor_get(v___x_1146_, 0);
v___x_1160_ = lean_usize_shift_right(v_x_1138_, v___x_1142_);
v_x_1137_ = v_node_1159_;
v_x_1138_ = v___x_1160_;
goto _start;
}
default: 
{
uint8_t v___x_1162_; 
v___x_1162_ = 0;
return v___x_1162_;
}
}
}
else
{
lean_object* v_ks_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_ks_1163_ = lean_ctor_get(v_x_1137_, 0);
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg(v_ks_1163_, v___x_1164_, v_x_1139_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___boxed(lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_){
_start:
{
size_t v_x_28210__boxed_1169_; uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_x_28210__boxed_1169_ = lean_unbox_usize(v_x_1167_);
lean_dec(v_x_1167_);
v_res_1170_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(v_x_1166_, v_x_28210__boxed_1169_, v_x_1168_);
lean_dec_ref(v_x_1168_);
lean_dec_ref(v_x_1166_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1172_; uint64_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(1723u);
v___x_1173_ = lean_uint64_of_nat(v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
uint64_t v___y_1177_; uint64_t v___y_1181_; uint64_t v___y_1185_; 
if (lean_obj_tag(v_x_1175_) == 0)
{
uint8_t v_inv_1188_; 
v_inv_1188_ = lean_ctor_get_uint8(v_x_1175_, sizeof(void*)*1 + 1);
if (v_inv_1188_ == 0)
{
lean_object* v_declName_1189_; 
v_declName_1189_ = lean_ctor_get(v_x_1175_, 0);
if (lean_obj_tag(v_declName_1189_) == 0)
{
uint64_t v___x_1190_; 
v___x_1190_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0);
v___y_1181_ = v___x_1190_;
goto v___jp_1180_;
}
else
{
uint64_t v_hash_1191_; 
v_hash_1191_ = lean_ctor_get_uint64(v_declName_1189_, sizeof(void*)*2);
v___y_1181_ = v_hash_1191_;
goto v___jp_1180_;
}
}
else
{
lean_object* v_declName_1192_; 
v_declName_1192_ = lean_ctor_get(v_x_1175_, 0);
if (lean_obj_tag(v_declName_1192_) == 0)
{
uint64_t v___x_1193_; 
v___x_1193_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0);
v___y_1185_ = v___x_1193_;
goto v___jp_1184_;
}
else
{
uint64_t v_hash_1194_; 
v_hash_1194_ = lean_ctor_get_uint64(v_declName_1192_, sizeof(void*)*2);
v___y_1185_ = v_hash_1194_;
goto v___jp_1184_;
}
}
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Meta_Origin_key(v_x_1175_);
if (lean_obj_tag(v___x_1195_) == 0)
{
uint64_t v___x_1196_; 
v___x_1196_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0);
v___y_1177_ = v___x_1196_;
goto v___jp_1176_;
}
else
{
uint64_t v_hash_1197_; 
v_hash_1197_ = lean_ctor_get_uint64(v___x_1195_, sizeof(void*)*2);
lean_dec(v___x_1195_);
v___y_1177_ = v_hash_1197_;
goto v___jp_1176_;
}
}
v___jp_1176_:
{
size_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_uint64_to_usize(v___y_1177_);
v___x_1179_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(v_x_1174_, v___x_1178_, v_x_1175_);
return v___x_1179_;
}
v___jp_1180_:
{
uint64_t v___x_1182_; uint64_t v___x_1183_; 
v___x_1182_ = 13ULL;
v___x_1183_ = lean_uint64_mix_hash(v___y_1181_, v___x_1182_);
v___y_1177_ = v___x_1183_;
goto v___jp_1176_;
}
v___jp_1184_:
{
uint64_t v___x_1186_; uint64_t v___x_1187_; 
v___x_1186_ = 11ULL;
v___x_1187_ = lean_uint64_mix_hash(v___y_1185_, v___x_1186_);
v___y_1177_ = v___x_1187_;
goto v___jp_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___boxed(lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_x_1198_, v_x_1199_);
lean_dec_ref(v_x_1199_);
lean_dec_ref(v_x_1198_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31___redArg(lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v_ks_1206_; lean_object* v_vs_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1231_; 
v_ks_1206_ = lean_ctor_get(v_x_1202_, 0);
v_vs_1207_ = lean_ctor_get(v_x_1202_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_x_1202_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1209_ = v_x_1202_;
v_isShared_1210_ = v_isSharedCheck_1231_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_vs_1207_);
lean_inc(v_ks_1206_);
lean_dec(v_x_1202_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1231_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_array_get_size(v_ks_1206_);
v___x_1212_ = lean_nat_dec_lt(v_x_1203_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_dec(v_x_1203_);
v___x_1213_ = lean_array_push(v_ks_1206_, v_x_1204_);
v___x_1214_ = lean_array_push(v_vs_1207_, v_x_1205_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1214_);
lean_ctor_set(v___x_1209_, 0, v___x_1213_);
v___x_1216_ = v___x_1209_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
else
{
lean_object* v_k_x27_1218_; uint8_t v___x_1219_; 
v_k_x27_1218_ = lean_array_fget_borrowed(v_ks_1206_, v_x_1203_);
v___x_1219_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1204_, v_k_x27_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1221_; 
if (v_isShared_1210_ == 0)
{
v___x_1221_ = v___x_1209_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_ks_1206_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_vs_1207_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_add(v_x_1203_, v___x_1222_);
lean_dec(v_x_1203_);
v_x_1202_ = v___x_1221_;
v_x_1203_ = v___x_1223_;
goto _start;
}
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1226_ = lean_array_fset(v_ks_1206_, v_x_1203_, v_x_1204_);
v___x_1227_ = lean_array_fset(v_vs_1207_, v_x_1203_, v_x_1205_);
lean_dec(v_x_1203_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1227_);
lean_ctor_set(v___x_1209_, 0, v___x_1226_);
v___x_1229_ = v___x_1209_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24___redArg(lean_object* v_n_1232_, lean_object* v_k_1233_, lean_object* v_v_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31___redArg(v_n_1232_, v___x_1235_, v_k_1233_, v_v_1234_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(lean_object* v_x_1238_, size_t v_x_1239_, size_t v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
lean_object* v_es_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; lean_object* v_j_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_es_1243_ = lean_ctor_get(v_x_1238_, 0);
v___x_1244_ = ((size_t)5ULL);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1);
v___x_1247_ = lean_usize_land(v_x_1239_, v___x_1246_);
v_j_1248_ = lean_usize_to_nat(v___x_1247_);
v___x_1249_ = lean_array_get_size(v_es_1243_);
v___x_1250_ = lean_nat_dec_lt(v_j_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_j_1248_);
lean_dec(v_x_1242_);
lean_dec(v_x_1241_);
return v_x_1238_;
}
else
{
lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1287_; 
lean_inc_ref(v_es_1243_);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_x_1238_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_x_1238_, 0);
lean_dec(v_unused_1288_);
v___x_1252_ = v_x_1238_;
v_isShared_1253_ = v_isSharedCheck_1287_;
goto v_resetjp_1251_;
}
else
{
lean_dec(v_x_1238_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1287_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_v_1254_; lean_object* v___x_1255_; lean_object* v_xs_x27_1256_; lean_object* v___y_1258_; 
v_v_1254_ = lean_array_fget(v_es_1243_, v_j_1248_);
v___x_1255_ = lean_box(0);
v_xs_x27_1256_ = lean_array_fset(v_es_1243_, v_j_1248_, v___x_1255_);
switch(lean_obj_tag(v_v_1254_))
{
case 0:
{
lean_object* v_key_1263_; lean_object* v_val_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1274_; 
v_key_1263_ = lean_ctor_get(v_v_1254_, 0);
v_val_1264_ = lean_ctor_get(v_v_1254_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_v_1254_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1266_ = v_v_1254_;
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_val_1264_);
lean_inc(v_key_1263_);
lean_dec(v_v_1254_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
uint8_t v___x_1268_; 
v___x_1268_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1241_, v_key_1263_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_del_object(v___x_1266_);
v___x_1269_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1263_, v_val_1264_, v_x_1241_, v_x_1242_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
v___y_1258_ = v___x_1270_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1272_; 
lean_dec(v_val_1264_);
lean_dec(v_key_1263_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_x_1242_);
lean_ctor_set(v___x_1266_, 0, v_x_1241_);
v___x_1272_ = v___x_1266_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_x_1241_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_x_1242_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
v___y_1258_ = v___x_1272_;
goto v___jp_1257_;
}
}
}
}
case 1:
{
lean_object* v_node_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1285_; 
v_node_1275_ = lean_ctor_get(v_v_1254_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_v_1254_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1277_ = v_v_1254_;
v_isShared_1278_ = v_isSharedCheck_1285_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_node_1275_);
lean_dec(v_v_1254_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1285_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1279_ = lean_usize_shift_right(v_x_1239_, v___x_1244_);
v___x_1280_ = lean_usize_add(v_x_1240_, v___x_1245_);
v___x_1281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_node_1275_, v___x_1279_, v___x_1280_, v_x_1241_, v_x_1242_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1281_);
v___x_1283_ = v___x_1277_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v___y_1258_ = v___x_1283_;
goto v___jp_1257_;
}
}
}
default: 
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_x_1241_);
lean_ctor_set(v___x_1286_, 1, v_x_1242_);
v___y_1258_ = v___x_1286_;
goto v___jp_1257_;
}
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_array_fset(v_xs_x27_1256_, v_j_1248_, v___y_1258_);
lean_dec(v_j_1248_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1259_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
else
{
lean_object* v_ks_1289_; lean_object* v_vs_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1310_; 
v_ks_1289_ = lean_ctor_get(v_x_1238_, 0);
v_vs_1290_ = lean_ctor_get(v_x_1238_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_x_1238_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1292_ = v_x_1238_;
v_isShared_1293_ = v_isSharedCheck_1310_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_vs_1290_);
lean_inc(v_ks_1289_);
lean_dec(v_x_1238_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1310_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_ks_1289_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_vs_1290_);
v___x_1295_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v_newNode_1296_; uint8_t v___y_1298_; size_t v___x_1304_; uint8_t v___x_1305_; 
v_newNode_1296_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24___redArg(v___x_1295_, v_x_1241_, v_x_1242_);
v___x_1304_ = ((size_t)7ULL);
v___x_1305_ = lean_usize_dec_le(v___x_1304_, v_x_1240_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1296_);
v___x_1307_ = lean_unsigned_to_nat(4u);
v___x_1308_ = lean_nat_dec_lt(v___x_1306_, v___x_1307_);
lean_dec(v___x_1306_);
v___y_1298_ = v___x_1308_;
goto v___jp_1297_;
}
else
{
v___y_1298_ = v___x_1305_;
goto v___jp_1297_;
}
v___jp_1297_:
{
if (v___y_1298_ == 0)
{
lean_object* v_ks_1299_; lean_object* v_vs_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_ks_1299_ = lean_ctor_get(v_newNode_1296_, 0);
lean_inc_ref(v_ks_1299_);
v_vs_1300_ = lean_ctor_get(v_newNode_1296_, 1);
lean_inc_ref(v_vs_1300_);
lean_dec_ref(v_newNode_1296_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___closed__0);
v___x_1303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg(v_x_1240_, v_ks_1299_, v_vs_1300_, v___x_1301_, v___x_1302_);
lean_dec_ref(v_vs_1300_);
lean_dec_ref(v_ks_1299_);
return v___x_1303_;
}
else
{
return v_newNode_1296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg(size_t v_depth_1311_, lean_object* v_keys_1312_, lean_object* v_vals_1313_, lean_object* v_i_1314_, lean_object* v_entries_1315_){
_start:
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_array_get_size(v_keys_1312_);
v___x_1317_ = lean_nat_dec_lt(v_i_1314_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec(v_i_1314_);
return v_entries_1315_;
}
else
{
lean_object* v_k_1318_; lean_object* v_v_1319_; uint64_t v___x_1320_; size_t v_h_1321_; size_t v___x_1322_; lean_object* v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v_h_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_k_1318_ = lean_array_fget_borrowed(v_keys_1312_, v_i_1314_);
v_v_1319_ = lean_array_fget_borrowed(v_vals_1313_, v_i_1314_);
v___x_1320_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1318_);
v_h_1321_ = lean_uint64_to_usize(v___x_1320_);
v___x_1322_ = ((size_t)5ULL);
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_sub(v_depth_1311_, v___x_1324_);
v___x_1326_ = lean_usize_mul(v___x_1322_, v___x_1325_);
v_h_1327_ = lean_usize_shift_right(v_h_1321_, v___x_1326_);
v___x_1328_ = lean_nat_add(v_i_1314_, v___x_1323_);
lean_dec(v_i_1314_);
lean_inc(v_v_1319_);
lean_inc(v_k_1318_);
v___x_1329_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_entries_1315_, v_h_1327_, v_depth_1311_, v_k_1318_, v_v_1319_);
v_i_1314_ = v___x_1328_;
v_entries_1315_ = v___x_1329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg___boxed(lean_object* v_depth_1331_, lean_object* v_keys_1332_, lean_object* v_vals_1333_, lean_object* v_i_1334_, lean_object* v_entries_1335_){
_start:
{
size_t v_depth_boxed_1336_; lean_object* v_res_1337_; 
v_depth_boxed_1336_ = lean_unbox_usize(v_depth_1331_);
lean_dec(v_depth_1331_);
v_res_1337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg(v_depth_boxed_1336_, v_keys_1332_, v_vals_1333_, v_i_1334_, v_entries_1335_);
lean_dec_ref(v_vals_1333_);
lean_dec_ref(v_keys_1332_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg___boxed(lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
size_t v_x_28416__boxed_1343_; size_t v_x_28417__boxed_1344_; lean_object* v_res_1345_; 
v_x_28416__boxed_1343_ = lean_unbox_usize(v_x_1339_);
lean_dec(v_x_1339_);
v_x_28417__boxed_1344_ = lean_unbox_usize(v_x_1340_);
lean_dec(v_x_1340_);
v_res_1345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_x_1338_, v_x_28416__boxed_1343_, v_x_28417__boxed_1344_, v_x_1341_, v_x_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
uint64_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1347_);
v___x_1350_ = lean_uint64_to_usize(v___x_1349_);
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_x_1346_, v___x_1350_, v___x_1351_, v_x_1347_, v_x_1348_);
return v___x_1352_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4(lean_object* v_msg_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4___closed__0);
v___x_1356_ = lean_panic_fn_borrowed(v___x_1355_, v_msg_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(lean_object* v_a_1357_, lean_object* v_b_1358_){
_start:
{
lean_object* v_fst_1359_; lean_object* v_fst_1360_; uint8_t v___x_1361_; 
v_fst_1359_ = lean_ctor_get(v_a_1357_, 0);
v_fst_1360_ = lean_ctor_get(v_b_1358_, 0);
v___x_1361_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1359_, v_fst_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1___boxed(lean_object* v_a_1362_, lean_object* v_b_1363_){
_start:
{
uint8_t v_res_1364_; lean_object* v_r_1365_; 
v_res_1364_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v_a_1362_, v_b_1363_);
lean_dec_ref(v_b_1363_);
lean_dec_ref(v_a_1362_);
v_r_1365_ = lean_box(v_res_1364_);
return v_r_1365_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0(lean_object* v_x_1366_, lean_object* v_keys_1367_, lean_object* v_v_1368_, lean_object* v_k_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_c_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_x_1366_, v___x_1371_);
v_c_1373_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1367_, v_v_1368_, v___x_1372_);
lean_dec(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_k_1369_);
lean_ctor_set(v___x_1374_, 1, v_c_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0___boxed(lean_object* v_x_1375_, lean_object* v_keys_1376_, lean_object* v_v_1377_, lean_object* v_k_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0(v_x_1375_, v_keys_1376_, v_v_1377_, v_k_1378_, v_x_1379_);
lean_dec_ref(v_keys_1376_);
lean_dec(v_x_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__16_spec__28(lean_object* v_vs_1381_, lean_object* v_v_1382_, lean_object* v_i_1383_){
_start:
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_array_get_size(v_vs_1381_);
v___x_1385_ = lean_nat_dec_lt(v_i_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec(v_i_1383_);
v___x_1386_ = lean_array_push(v_vs_1381_, v_v_1382_);
return v___x_1386_;
}
else
{
lean_object* v_proof_1387_; lean_object* v___x_1388_; lean_object* v_proof_1389_; uint8_t v___x_1390_; 
v_proof_1387_ = lean_ctor_get(v_v_1382_, 1);
v___x_1388_ = lean_array_fget_borrowed(v_vs_1381_, v_i_1383_);
v_proof_1389_ = lean_ctor_get(v___x_1388_, 1);
lean_inc_ref(v_proof_1389_);
lean_inc_ref(v_proof_1387_);
v___x_1390_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_1387_, v_proof_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_i_1383_, v___x_1391_);
lean_dec(v_i_1383_);
v_i_1383_ = v___x_1392_;
goto _start;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_array_fset(v_vs_1381_, v_i_1383_, v_v_1382_);
lean_dec(v_i_1383_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__16(lean_object* v_vs_1395_, lean_object* v_v_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__16_spec__28(v_vs_1395_, v_v_1396_, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg(lean_object* v_x_1403_, lean_object* v_keys_1404_, lean_object* v_v_1405_, lean_object* v_k_1406_, lean_object* v_as_1407_, lean_object* v_k_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_mid_1413_; lean_object* v_midVal_1414_; uint8_t v___x_1415_; 
v___x_1411_ = lean_nat_add(v_x_1409_, v_x_1410_);
v___x_1412_ = lean_unsigned_to_nat(1u);
v_mid_1413_ = lean_nat_shiftr(v___x_1411_, v___x_1412_);
lean_dec(v___x_1411_);
v_midVal_1414_ = lean_array_fget(v_as_1407_, v_mid_1413_);
v___x_1415_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v_midVal_1414_, v_k_1408_);
if (v___x_1415_ == 0)
{
uint8_t v___x_1416_; 
lean_dec(v_x_1410_);
v___x_1416_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v_k_1408_, v_midVal_1414_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
lean_dec(v_x_1409_);
v___x_1417_ = lean_array_get_size(v_as_1407_);
v___x_1418_ = lean_nat_dec_lt(v_mid_1413_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec(v_midVal_1414_);
lean_dec(v_mid_1413_);
lean_dec(v_k_1406_);
lean_dec_ref(v_v_1405_);
return v_as_1407_;
}
else
{
lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1431_; 
v_snd_1419_ = lean_ctor_get(v_midVal_1414_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_midVal_1414_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_midVal_1414_, 0);
lean_dec(v_unused_1432_);
v___x_1421_ = v_midVal_1414_;
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_dec(v_midVal_1414_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v_xs_x27_1424_; lean_object* v___x_1425_; lean_object* v_c_1426_; lean_object* v___x_1428_; 
v___x_1423_ = lean_box(0);
v_xs_x27_1424_ = lean_array_fset(v_as_1407_, v_mid_1413_, v___x_1423_);
v___x_1425_ = lean_nat_add(v_x_1403_, v___x_1412_);
v_c_1426_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3(v_keys_1404_, v_v_1405_, v___x_1425_, v_snd_1419_);
lean_dec(v___x_1425_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v_c_1426_);
lean_ctor_set(v___x_1421_, 0, v_k_1406_);
v___x_1428_ = v___x_1421_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_c_1426_);
v___x_1428_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_array_fset(v_xs_x27_1424_, v_mid_1413_, v___x_1428_);
lean_dec(v_mid_1413_);
return v___x_1429_;
}
}
}
}
else
{
lean_dec(v_midVal_1414_);
v_x_1410_ = v_mid_1413_;
goto _start;
}
}
else
{
uint8_t v___x_1434_; 
lean_dec(v_midVal_1414_);
v___x_1434_ = lean_nat_dec_eq(v_mid_1413_, v_x_1409_);
if (v___x_1434_ == 0)
{
lean_dec(v_x_1409_);
v_x_1409_ = v_mid_1413_;
goto _start;
}
else
{
lean_object* v___x_1436_; lean_object* v_c_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v_j_1440_; lean_object* v_as_1441_; lean_object* v___x_1442_; 
lean_dec(v_mid_1413_);
lean_dec(v_x_1410_);
v___x_1436_ = lean_nat_add(v_x_1403_, v___x_1412_);
v_c_1437_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1404_, v_v_1405_, v___x_1436_);
lean_dec(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_k_1406_);
lean_ctor_set(v___x_1438_, 1, v_c_1437_);
v___x_1439_ = lean_nat_add(v_x_1409_, v___x_1412_);
lean_dec(v_x_1409_);
v_j_1440_ = lean_array_get_size(v_as_1407_);
v_as_1441_ = lean_array_push(v_as_1407_, v___x_1438_);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1439_, v_as_1441_, v_j_1440_);
lean_dec(v___x_1439_);
return v___x_1442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17(lean_object* v_x_1443_, lean_object* v_keys_1444_, lean_object* v_v_1445_, lean_object* v_k_1446_, lean_object* v_as_1447_, lean_object* v_k_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_array_get_size(v_as_1447_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = lean_nat_dec_eq(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = lean_array_fget_borrowed(v_as_1447_, v___x_1450_);
v___x_1453_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v_k_1448_, v___x_1452_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v___x_1452_, v_k_1448_);
if (v___x_1454_ == 0)
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_nat_dec_lt(v___x_1450_, v___x_1449_);
if (v___x_1455_ == 0)
{
lean_dec(v_k_1446_);
lean_dec_ref(v_v_1445_);
return v_as_1447_;
}
else
{
lean_object* v___x_1456_; lean_object* v_xs_x27_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_inc(v___x_1452_);
v___x_1456_ = lean_box(0);
v_xs_x27_1457_ = lean_array_fset(v_as_1447_, v___x_1450_, v___x_1456_);
v___x_1458_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2(v_x_1443_, v_keys_1444_, v_v_1445_, v_k_1446_, v___x_1452_);
v___x_1459_ = lean_array_fset(v_xs_x27_1457_, v___x_1450_, v___x_1458_);
return v___x_1459_;
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_sub(v___x_1449_, v___x_1460_);
v___x_1462_ = lean_array_fget_borrowed(v_as_1447_, v___x_1461_);
v___x_1463_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v___x_1462_, v_k_1448_);
if (v___x_1463_ == 0)
{
uint8_t v___x_1464_; 
v___x_1464_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__1(v_k_1448_, v___x_1462_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_nat_dec_lt(v___x_1461_, v___x_1449_);
if (v___x_1465_ == 0)
{
lean_dec(v___x_1461_);
lean_dec(v_k_1446_);
lean_dec_ref(v_v_1445_);
return v_as_1447_;
}
else
{
lean_object* v___x_1466_; lean_object* v_xs_x27_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_inc(v___x_1462_);
v___x_1466_ = lean_box(0);
v_xs_x27_1467_ = lean_array_fset(v_as_1447_, v___x_1461_, v___x_1466_);
v___x_1468_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2(v_x_1443_, v_keys_1444_, v_v_1445_, v_k_1446_, v___x_1462_);
v___x_1469_ = lean_array_fset(v_xs_x27_1467_, v___x_1461_, v___x_1468_);
lean_dec(v___x_1461_);
return v___x_1469_;
}
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg(v_x_1443_, v_keys_1444_, v_v_1445_, v_k_1446_, v_as_1447_, v_k_1448_, v___x_1450_, v___x_1461_);
return v___x_1470_;
}
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1461_);
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0(v_x_1443_, v_keys_1444_, v_v_1445_, v_k_1446_, v___x_1471_);
v___x_1473_ = lean_array_push(v_as_1447_, v___x_1472_);
return v___x_1473_;
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_as_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0(v_x_1443_, v_keys_1444_, v_v_1445_, v_k_1446_, v___x_1474_);
v_as_1476_ = lean_array_push(v_as_1447_, v___x_1475_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1450_, v_as_1476_, v___x_1449_);
return v___x_1477_;
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = lean_box(0);
v___x_1479_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__0(v_x_1443_, v_keys_1444_, v_v_1445_, v_k_1446_, v___x_1478_);
v___x_1480_ = lean_array_push(v_as_1447_, v___x_1479_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3(lean_object* v_keys_1481_, lean_object* v_v_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
lean_object* v_vs_1485_; lean_object* v_children_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1503_; 
v_vs_1485_ = lean_ctor_get(v_x_1484_, 0);
v_children_1486_ = lean_ctor_get(v_x_1484_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_x_1484_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1488_ = v_x_1484_;
v_isShared_1489_ = v_isSharedCheck_1503_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_children_1486_);
lean_inc(v_vs_1485_);
lean_dec(v_x_1484_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1503_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = lean_array_get_size(v_keys_1481_);
v___x_1491_ = lean_nat_dec_lt(v_x_1483_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__16(v_vs_1485_, v_v_1482_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1492_);
v___x_1494_ = v___x_1488_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_children_1486_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
else
{
lean_object* v_k_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_c_1499_; lean_object* v___x_1501_; 
v_k_1496_ = lean_array_fget_borrowed(v_keys_1481_, v_x_1483_);
v___x_1497_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___closed__1));
lean_inc_n(v_k_1496_, 2);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_k_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v_c_1499_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17(v_x_1483_, v_keys_1481_, v_v_1482_, v_k_1496_, v_children_1486_, v___x_1498_);
lean_dec_ref(v___x_1498_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v_c_1499_);
v___x_1501_ = v___x_1488_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_vs_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_c_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2(lean_object* v_x_1504_, lean_object* v_keys_1505_, lean_object* v_v_1506_, lean_object* v_k_1507_, lean_object* v_x_1508_){
_start:
{
lean_object* v_snd_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1519_; 
v_snd_1509_ = lean_ctor_get(v_x_1508_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1508_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_x_1508_, 0);
lean_dec(v_unused_1520_);
v___x_1511_ = v_x_1508_;
v_isShared_1512_ = v_isSharedCheck_1519_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_snd_1509_);
lean_dec(v_x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1519_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_c_1515_; lean_object* v___x_1517_; 
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_nat_add(v_x_1504_, v___x_1513_);
v_c_1515_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3(v_keys_1505_, v_v_1506_, v___x_1514_, v_snd_1509_);
lean_dec(v___x_1514_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v_c_1515_);
lean_ctor_set(v___x_1511_, 0, v_k_1507_);
v___x_1517_ = v___x_1511_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_c_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2___boxed(lean_object* v_x_1521_, lean_object* v_keys_1522_, lean_object* v_v_1523_, lean_object* v_k_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___lam__2(v_x_1521_, v_keys_1522_, v_v_1523_, v_k_1524_, v_x_1525_);
lean_dec_ref(v_keys_1522_);
lean_dec(v_x_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3___boxed(lean_object* v_keys_1527_, lean_object* v_v_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3(v_keys_1527_, v_v_1528_, v_x_1529_, v_x_1530_);
lean_dec(v_x_1529_);
lean_dec_ref(v_keys_1527_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg___boxed(lean_object* v_x_1532_, lean_object* v_keys_1533_, lean_object* v_v_1534_, lean_object* v_k_1535_, lean_object* v_as_1536_, lean_object* v_k_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg(v_x_1532_, v_keys_1533_, v_v_1534_, v_k_1535_, v_as_1536_, v_k_1537_, v_x_1538_, v_x_1539_);
lean_dec_ref(v_k_1537_);
lean_dec_ref(v_keys_1533_);
lean_dec(v_x_1532_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_x_1541_, lean_object* v_keys_1542_, lean_object* v_v_1543_, lean_object* v_k_1544_, lean_object* v_as_1545_, lean_object* v_k_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17(v_x_1541_, v_keys_1542_, v_v_1543_, v_k_1544_, v_as_1545_, v_k_1546_);
lean_dec_ref(v_k_1546_);
lean_dec_ref(v_keys_1542_);
lean_dec(v_x_1541_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg(lean_object* v_keys_1548_, lean_object* v_vals_1549_, lean_object* v_i_1550_, lean_object* v_k_1551_){
_start:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_keys_1548_);
v___x_1553_ = lean_nat_dec_lt(v_i_1550_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_i_1550_);
v___x_1554_ = lean_box(0);
return v___x_1554_;
}
else
{
lean_object* v_k_x27_1555_; uint8_t v___x_1556_; 
v_k_x27_1555_ = lean_array_fget_borrowed(v_keys_1548_, v_i_1550_);
v___x_1556_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1551_, v_k_x27_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_i_1550_, v___x_1557_);
lean_dec(v_i_1550_);
v_i_1550_ = v___x_1558_;
goto _start;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_array_fget_borrowed(v_vals_1549_, v_i_1550_);
lean_dec(v_i_1550_);
lean_inc(v___x_1560_);
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg___boxed(lean_object* v_keys_1562_, lean_object* v_vals_1563_, lean_object* v_i_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg(v_keys_1562_, v_vals_1563_, v_i_1564_, v_k_1565_);
lean_dec(v_k_1565_);
lean_dec_ref(v_vals_1563_);
lean_dec_ref(v_keys_1562_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(lean_object* v_x_1567_, size_t v_x_1568_, lean_object* v_x_1569_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
lean_object* v_es_1570_; lean_object* v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; lean_object* v_j_1575_; lean_object* v___x_1576_; 
v_es_1570_ = lean_ctor_get(v_x_1567_, 0);
v___x_1571_ = lean_box(2);
v___x_1572_ = ((size_t)5ULL);
v___x_1573_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1);
v___x_1574_ = lean_usize_land(v_x_1568_, v___x_1573_);
v_j_1575_ = lean_usize_to_nat(v___x_1574_);
v___x_1576_ = lean_array_get_borrowed(v___x_1571_, v_es_1570_, v_j_1575_);
lean_dec(v_j_1575_);
switch(lean_obj_tag(v___x_1576_))
{
case 0:
{
lean_object* v_key_1577_; lean_object* v_val_1578_; uint8_t v___x_1579_; 
v_key_1577_ = lean_ctor_get(v___x_1576_, 0);
v_val_1578_ = lean_ctor_get(v___x_1576_, 1);
v___x_1579_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1569_, v_key_1577_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; 
lean_inc(v_val_1578_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_val_1578_);
return v___x_1581_;
}
}
case 1:
{
lean_object* v_node_1582_; size_t v___x_1583_; 
v_node_1582_ = lean_ctor_get(v___x_1576_, 0);
v___x_1583_ = lean_usize_shift_right(v_x_1568_, v___x_1572_);
v_x_1567_ = v_node_1582_;
v_x_1568_ = v___x_1583_;
goto _start;
}
default: 
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_box(0);
return v___x_1585_;
}
}
}
else
{
lean_object* v_ks_1586_; lean_object* v_vs_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_ks_1586_ = lean_ctor_get(v_x_1567_, 0);
v_vs_1587_ = lean_ctor_get(v_x_1567_, 1);
v___x_1588_ = lean_unsigned_to_nat(0u);
v___x_1589_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg(v_ks_1586_, v_vs_1587_, v___x_1588_, v_x_1569_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg___boxed(lean_object* v_x_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
size_t v_x_28857__boxed_1593_; lean_object* v_res_1594_; 
v_x_28857__boxed_1593_ = lean_unbox_usize(v_x_1591_);
lean_dec(v_x_1591_);
v_res_1594_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(v_x_1590_, v_x_28857__boxed_1593_, v_x_1592_);
lean_dec(v_x_1592_);
lean_dec_ref(v_x_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
uint64_t v___x_1597_; size_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1596_);
v___x_1598_ = lean_uint64_to_usize(v___x_1597_);
v___x_1599_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(v_x_1595_, v___x_1598_, v_x_1596_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_x_1600_, v_x_1601_);
lean_dec(v_x_1601_);
lean_dec_ref(v_x_1600_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1606_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__2));
v___x_1607_ = lean_unsigned_to_nat(23u);
v___x_1608_ = lean_unsigned_to_nat(166u);
v___x_1609_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__1));
v___x_1610_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__0));
v___x_1611_ = l_mkPanicMessageWithDecl(v___x_1610_, v___x_1609_, v___x_1608_, v___x_1607_, v___x_1606_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(lean_object* v_d_1612_, lean_object* v_keys_1613_, lean_object* v_v_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_array_get_size(v_keys_1613_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_nat_dec_eq(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v_k_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_box(0);
v_k_1619_ = lean_array_get_borrowed(v___x_1618_, v_keys_1613_, v___x_1616_);
v___x_1620_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_d_1612_, v_k_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1621_; lean_object* v_c_1622_; lean_object* v___x_1623_; 
v___x_1621_ = lean_unsigned_to_nat(1u);
v_c_1622_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1613_, v_v_1614_, v___x_1621_);
lean_inc(v_k_1619_);
v___x_1623_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_d_1612_, v_k_1619_, v_c_1622_);
return v___x_1623_;
}
else
{
lean_object* v_val_1624_; lean_object* v___x_1625_; lean_object* v_c_1626_; lean_object* v___x_1627_; 
v_val_1624_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v___x_1620_);
v___x_1625_ = lean_unsigned_to_nat(1u);
v_c_1626_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3(v_keys_1613_, v_v_1614_, v___x_1625_, v_val_1624_);
lean_inc(v_k_1619_);
v___x_1627_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_d_1612_, v_k_1619_, v_c_1626_);
return v___x_1627_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec_ref(v_v_1614_);
lean_dec_ref(v_d_1612_);
v___x_1628_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___closed__3);
v___x_1629_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__4(v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___boxed(lean_object* v_d_1630_, lean_object* v_keys_1631_, lean_object* v_v_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(v_d_1630_, v_keys_1631_, v_v_1632_);
lean_dec_ref(v_keys_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(lean_object* v_d_1634_, lean_object* v_p_1635_, lean_object* v_v_1636_){
_start:
{
lean_object* v_keys_1637_; lean_object* v___x_1638_; 
v_keys_1637_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_1635_);
v___x_1638_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(v_d_1634_, v_keys_1637_, v_v_1636_);
lean_dec_ref(v_keys_1637_);
return v___x_1638_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1639_; double v___x_1640_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_float_of_nat(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(lean_object* v_cls_1644_, lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_ref_1651_; lean_object* v___x_1652_; lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1698_; 
v_ref_1651_ = lean_ctor_get(v___y_1648_, 5);
v___x_1652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1698_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1698_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v_traceState_1658_; lean_object* v_env_1659_; lean_object* v_nextMacroScope_1660_; lean_object* v_ngen_1661_; lean_object* v_auxDeclNGen_1662_; lean_object* v_cache_1663_; lean_object* v_messages_1664_; lean_object* v_infoState_1665_; lean_object* v_snapshotTasks_1666_; lean_object* v_newDecls_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1697_; 
v___x_1657_ = lean_st_ref_take(v___y_1649_);
v_traceState_1658_ = lean_ctor_get(v___x_1657_, 4);
v_env_1659_ = lean_ctor_get(v___x_1657_, 0);
v_nextMacroScope_1660_ = lean_ctor_get(v___x_1657_, 1);
v_ngen_1661_ = lean_ctor_get(v___x_1657_, 2);
v_auxDeclNGen_1662_ = lean_ctor_get(v___x_1657_, 3);
v_cache_1663_ = lean_ctor_get(v___x_1657_, 5);
v_messages_1664_ = lean_ctor_get(v___x_1657_, 6);
v_infoState_1665_ = lean_ctor_get(v___x_1657_, 7);
v_snapshotTasks_1666_ = lean_ctor_get(v___x_1657_, 8);
v_newDecls_1667_ = lean_ctor_get(v___x_1657_, 9);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1669_ = v___x_1657_;
v_isShared_1670_ = v_isSharedCheck_1697_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_newDecls_1667_);
lean_inc(v_snapshotTasks_1666_);
lean_inc(v_infoState_1665_);
lean_inc(v_messages_1664_);
lean_inc(v_cache_1663_);
lean_inc(v_traceState_1658_);
lean_inc(v_auxDeclNGen_1662_);
lean_inc(v_ngen_1661_);
lean_inc(v_nextMacroScope_1660_);
lean_inc(v_env_1659_);
lean_dec(v___x_1657_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1697_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
uint64_t v_tid_1671_; lean_object* v_traces_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1696_; 
v_tid_1671_ = lean_ctor_get_uint64(v_traceState_1658_, sizeof(void*)*1);
v_traces_1672_ = lean_ctor_get(v_traceState_1658_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_traceState_1658_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1674_ = v_traceState_1658_;
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_traces_1672_);
lean_dec(v_traceState_1658_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; double v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0);
v___x_1678_ = 0;
v___x_1679_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1));
v___x_1680_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1680_, 0, v_cls_1644_);
lean_ctor_set(v___x_1680_, 1, v___x_1676_);
lean_ctor_set(v___x_1680_, 2, v___x_1679_);
lean_ctor_set_float(v___x_1680_, sizeof(void*)*3, v___x_1677_);
lean_ctor_set_float(v___x_1680_, sizeof(void*)*3 + 8, v___x_1677_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*3 + 16, v___x_1678_);
v___x_1681_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2));
v___x_1682_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v_a_1653_);
lean_ctor_set(v___x_1682_, 2, v___x_1681_);
lean_inc(v_ref_1651_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_ref_1651_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_PersistentArray_push___redArg(v_traces_1672_, v___x_1683_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1684_);
v___x_1686_ = v___x_1674_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1684_);
lean_ctor_set_uint64(v_reuseFailAlloc_1695_, sizeof(void*)*1, v_tid_1671_);
v___x_1686_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 4, v___x_1686_);
v___x_1688_ = v___x_1669_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_env_1659_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_nextMacroScope_1660_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_ngen_1661_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_auxDeclNGen_1662_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v_cache_1663_);
lean_ctor_set(v_reuseFailAlloc_1694_, 6, v_messages_1664_);
lean_ctor_set(v_reuseFailAlloc_1694_, 7, v_infoState_1665_);
lean_ctor_set(v_reuseFailAlloc_1694_, 8, v_snapshotTasks_1666_);
lean_ctor_set(v_reuseFailAlloc_1694_, 9, v_newDecls_1667_);
v___x_1688_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1689_ = lean_st_ref_set(v___y_1649_, v___x_1688_);
v___x_1690_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1690_);
v___x_1692_ = v___x_1655_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___boxed(lean_object* v_cls_1699_, lean_object* v_msg_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_1699_, v_msg_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1706_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5));
v___x_1720_ = l_Lean_Name_append(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(lean_object* v_simpThms_1727_, lean_object* v_as_1728_, size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_a_1740_; uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1731_);
return v___x_1745_;
}
else
{
lean_object* v_a_1746_; lean_object* v_origin_1747_; 
v_a_1746_ = lean_array_uget_borrowed(v_as_1728_, v_i_1730_);
v_origin_1747_ = lean_ctor_get(v_a_1746_, 4);
if (lean_obj_tag(v_origin_1747_) == 0)
{
lean_object* v_priority_1748_; lean_object* v_declName_1749_; lean_object* v_erased_1750_; uint8_t v___x_1751_; 
v_priority_1748_ = lean_ctor_get(v_a_1746_, 3);
v_declName_1749_ = lean_ctor_get(v_origin_1747_, 0);
v_erased_1750_ = lean_ctor_get(v_simpThms_1727_, 4);
v___x_1751_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_erased_1750_, v_origin_1747_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_inc(v_priority_1748_);
lean_inc(v_declName_1749_);
v___x_1752_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_declName_1749_, v_priority_1748_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
if (lean_obj_tag(v_a_1753_) == 1)
{
lean_object* v_val_1754_; lean_object* v_pattern_1755_; lean_object* v___x_1756_; 
v_val_1754_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_val_1754_);
lean_dec_ref(v_a_1753_);
v_pattern_1755_ = lean_ctor_get(v_val_1754_, 0);
lean_inc_ref(v_pattern_1755_);
v___x_1756_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(v_b_1731_, v_pattern_1755_, v_val_1754_);
v_a_1740_ = v___x_1756_;
goto v___jp_1739_;
}
else
{
lean_dec(v_a_1753_);
v_a_1740_ = v_b_1731_;
goto v___jp_1739_;
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1790_; 
v_a_1757_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1759_ = v___x_1752_;
v_isShared_1760_ = v_isSharedCheck_1790_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1752_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1790_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint8_t v___y_1762_; uint8_t v___x_1788_; 
v___x_1788_ = l_Lean_Exception_isInterrupt(v_a_1757_);
if (v___x_1788_ == 0)
{
uint8_t v___x_1789_; 
lean_inc(v_a_1757_);
v___x_1789_ = l_Lean_Exception_isRuntime(v_a_1757_);
v___y_1762_ = v___x_1789_;
goto v___jp_1761_;
}
else
{
v___y_1762_ = v___x_1788_;
goto v___jp_1761_;
}
v___jp_1761_:
{
if (v___y_1762_ == 0)
{
lean_object* v_options_1763_; uint8_t v_hasTrace_1764_; 
lean_del_object(v___x_1759_);
v_options_1763_ = lean_ctor_get(v___y_1736_, 2);
v_hasTrace_1764_ = lean_ctor_get_uint8(v_options_1763_, sizeof(void*)*1);
if (v_hasTrace_1764_ == 0)
{
lean_dec(v_a_1757_);
v_a_1740_ = v_b_1731_;
goto v___jp_1739_;
}
else
{
lean_object* v_inheritedTraceOptions_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_inheritedTraceOptions_1765_ = lean_ctor_get(v___y_1736_, 13);
v___x_1766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1767_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_1768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1765_, v_options_1763_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec(v_a_1757_);
v_a_1740_ = v_b_1731_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1769_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8);
lean_inc(v_declName_1749_);
v___x_1770_ = l_Lean_MessageData_ofName(v_declName_1749_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_Exception_toMessageData(v_a_1757_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_1766_, v___x_1775_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_dec_ref(v___x_1776_);
v_a_1740_ = v_b_1731_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v_b_1731_);
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
else
{
lean_object* v___x_1786_; 
lean_dec_ref(v_b_1731_);
if (v_isShared_1760_ == 0)
{
v___x_1786_ = v___x_1759_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1757_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
else
{
v_a_1740_ = v_b_1731_;
goto v___jp_1739_;
}
}
else
{
v_a_1740_ = v_b_1731_;
goto v___jp_1739_;
}
}
v___jp_1739_:
{
size_t v___x_1741_; size_t v___x_1742_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1730_, v___x_1741_);
v_i_1730_ = v___x_1742_;
v_b_1731_ = v_a_1740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(lean_object* v_simpThms_1791_, lean_object* v_as_1792_, lean_object* v_sz_1793_, lean_object* v_i_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
size_t v_sz_boxed_1803_; size_t v_i_boxed_1804_; lean_object* v_res_1805_; 
v_sz_boxed_1803_ = lean_unbox_usize(v_sz_1793_);
lean_dec(v_sz_1793_);
v_i_boxed_1804_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_simpThms_1791_, v_as_1792_, v_sz_boxed_1803_, v_i_boxed_1804_, v_b_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_as_1792_);
lean_dec_ref(v_simpThms_1791_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
if (lean_obj_tag(v_a_1806_) == 0)
{
lean_object* v___x_1808_; 
v___x_1808_ = l_List_reverse___redArg(v_a_1807_);
return v___x_1808_;
}
else
{
lean_object* v_head_1809_; lean_object* v_tail_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1819_; 
v_head_1809_ = lean_ctor_get(v_a_1806_, 0);
v_tail_1810_ = lean_ctor_get(v_a_1806_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_a_1806_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1812_ = v_a_1806_;
v_isShared_1813_ = v_isSharedCheck_1819_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_tail_1810_);
lean_inc(v_head_1809_);
lean_dec(v_a_1806_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1819_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_fst_1814_; lean_object* v___x_1816_; 
v_fst_1814_ = lean_ctor_get(v_head_1809_, 0);
lean_inc(v_fst_1814_);
lean_dec(v_head_1809_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v_a_1807_);
lean_ctor_set(v___x_1812_, 0, v_fst_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_fst_1814_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1807_);
v___x_1816_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
v_a_1806_ = v_tail_1810_;
v_a_1807_ = v___x_1816_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0(lean_object* v_f_1820_, lean_object* v_x1_1821_, lean_object* v_x2_1822_, lean_object* v_x3_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_apply_3(v_f_1820_, v_x1_1821_, v_x2_1822_, v_x3_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(lean_object* v_f_1825_, lean_object* v_keys_1826_, lean_object* v_vals_1827_, lean_object* v_i_1828_, lean_object* v_acc_1829_){
_start:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_array_get_size(v_keys_1826_);
v___x_1831_ = lean_nat_dec_lt(v_i_1828_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_dec(v_i_1828_);
lean_dec(v_f_1825_);
return v_acc_1829_;
}
else
{
lean_object* v_k_1832_; lean_object* v_v_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_k_1832_ = lean_array_fget_borrowed(v_keys_1826_, v_i_1828_);
v_v_1833_ = lean_array_fget_borrowed(v_vals_1827_, v_i_1828_);
lean_inc(v_f_1825_);
lean_inc(v_v_1833_);
lean_inc(v_k_1832_);
v___x_1834_ = lean_apply_3(v_f_1825_, v_acc_1829_, v_k_1832_, v_v_1833_);
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_nat_add(v_i_1828_, v___x_1835_);
lean_dec(v_i_1828_);
v_i_1828_ = v___x_1836_;
v_acc_1829_ = v___x_1834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v_f_1838_, lean_object* v_keys_1839_, lean_object* v_vals_1840_, lean_object* v_i_1841_, lean_object* v_acc_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1838_, v_keys_1839_, v_vals_1840_, v_i_1841_, v_acc_1842_);
lean_dec_ref(v_vals_1840_);
lean_dec_ref(v_keys_1839_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(lean_object* v_f_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1845_) == 0)
{
lean_object* v_es_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_es_1847_ = lean_ctor_get(v_x_1845_, 0);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_array_get_size(v_es_1847_);
v___x_1850_ = lean_nat_dec_lt(v___x_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_dec(v_f_1844_);
return v_x_1846_;
}
else
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_nat_dec_le(v___x_1849_, v___x_1849_);
if (v___x_1851_ == 0)
{
if (v___x_1850_ == 0)
{
lean_dec(v_f_1844_);
return v_x_1846_;
}
else
{
size_t v___x_1852_; size_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = lean_usize_of_nat(v___x_1849_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1844_, v_es_1847_, v___x_1852_, v___x_1853_, v_x_1846_);
return v___x_1854_;
}
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1849_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1844_, v_es_1847_, v___x_1855_, v___x_1856_, v_x_1846_);
return v___x_1857_;
}
}
}
else
{
lean_object* v_ks_1858_; lean_object* v_vs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_ks_1858_ = lean_ctor_get(v_x_1845_, 0);
v_vs_1859_ = lean_ctor_get(v_x_1845_, 1);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1844_, v_ks_1858_, v_vs_1859_, v___x_1860_, v_x_1846_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(lean_object* v_f_1862_, lean_object* v_as_1863_, size_t v_i_1864_, size_t v_stop_1865_, lean_object* v_b_1866_){
_start:
{
lean_object* v___y_1868_; uint8_t v___x_1872_; 
v___x_1872_ = lean_usize_dec_eq(v_i_1864_, v_stop_1865_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_array_uget_borrowed(v_as_1863_, v_i_1864_);
switch(lean_obj_tag(v___x_1873_))
{
case 0:
{
lean_object* v_key_1874_; lean_object* v_val_1875_; lean_object* v___x_1876_; 
v_key_1874_ = lean_ctor_get(v___x_1873_, 0);
v_val_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_f_1862_);
lean_inc(v_val_1875_);
lean_inc(v_key_1874_);
v___x_1876_ = lean_apply_3(v_f_1862_, v_b_1866_, v_key_1874_, v_val_1875_);
v___y_1868_ = v___x_1876_;
goto v___jp_1867_;
}
case 1:
{
lean_object* v_node_1877_; lean_object* v___x_1878_; 
v_node_1877_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_f_1862_);
v___x_1878_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_1862_, v_node_1877_, v_b_1866_);
v___y_1868_ = v___x_1878_;
goto v___jp_1867_;
}
default: 
{
v___y_1868_ = v_b_1866_;
goto v___jp_1867_;
}
}
}
else
{
lean_dec(v_f_1862_);
return v_b_1866_;
}
v___jp_1867_:
{
size_t v___x_1869_; size_t v___x_1870_; 
v___x_1869_ = ((size_t)1ULL);
v___x_1870_ = lean_usize_add(v_i_1864_, v___x_1869_);
v_i_1864_ = v___x_1870_;
v_b_1866_ = v___y_1868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg___boxed(lean_object* v_f_1879_, lean_object* v_as_1880_, lean_object* v_i_1881_, lean_object* v_stop_1882_, lean_object* v_b_1883_){
_start:
{
size_t v_i_boxed_1884_; size_t v_stop_boxed_1885_; lean_object* v_res_1886_; 
v_i_boxed_1884_ = lean_unbox_usize(v_i_1881_);
lean_dec(v_i_1881_);
v_stop_boxed_1885_ = lean_unbox_usize(v_stop_1882_);
lean_dec(v_stop_1882_);
v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1879_, v_as_1880_, v_i_boxed_1884_, v_stop_boxed_1885_, v_b_1883_);
lean_dec_ref(v_as_1880_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(lean_object* v_f_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_1887_, v_x_1888_, v_x_1889_);
lean_dec_ref(v_x_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(lean_object* v_map_1891_, lean_object* v_f_1892_, lean_object* v_init_1893_){
_start:
{
lean_object* v___f_1894_; lean_object* v___x_1895_; 
v___f_1894_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1894_, 0, v_f_1892_);
v___x_1895_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_1894_, v_map_1891_, v_init_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___boxed(lean_object* v_map_1896_, lean_object* v_f_1897_, lean_object* v_init_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_map_1896_, v_f_1897_, v_init_1898_);
lean_dec_ref(v_map_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0(lean_object* v_ps_1900_, lean_object* v_k_1901_, lean_object* v_v_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v_k_1901_);
lean_ctor_set(v___x_1903_, 1, v_v_1902_);
v___x_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v_ps_1900_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(lean_object* v_m_1906_){
_start:
{
lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___f_1907_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0));
v___x_1908_ = lean_box(0);
v___x_1909_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_m_1906_, v___f_1907_, v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___boxed(lean_object* v_m_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_1910_);
lean_dec_ref(v_m_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(lean_object* v_s_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_s_1912_);
v___x_1914_ = lean_box(0);
v___x_1915_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(v___x_1913_, v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9___boxed(lean_object* v_s_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_s_1916_);
lean_dec_ref(v_s_1916_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(lean_object* v_database_1918_, lean_object* v_as_1919_, size_t v_sz_1920_, size_t v_i_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_a_1931_; uint8_t v___x_1935_; 
v___x_1935_ = lean_usize_dec_lt(v_i_1921_, v_sz_1920_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v_database_1918_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_b_1922_);
return v___x_1936_;
}
else
{
lean_object* v_a_1937_; lean_object* v_proof_1938_; lean_object* v_priority_1939_; uint8_t v___x_1940_; 
v_a_1937_ = lean_array_uget_borrowed(v_as_1919_, v_i_1921_);
v_proof_1938_ = lean_ctor_get(v_a_1937_, 2);
v_priority_1939_ = lean_ctor_get(v_a_1937_, 4);
lean_inc_ref(v_proof_1938_);
lean_inc_ref(v_database_1918_);
v___x_1940_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_database_1918_, v_proof_1938_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_inc(v_priority_1939_);
lean_inc_ref(v_proof_1938_);
v___x_1941_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(v_proof_1938_, v_priority_1939_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_pattern_1943_; lean_object* v___x_1944_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v_pattern_1943_ = lean_ctor_get(v_a_1942_, 0);
lean_inc_ref(v_pattern_1943_);
v___x_1944_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(v_b_1922_, v_pattern_1943_, v_a_1942_);
v_a_1931_ = v___x_1944_;
goto v___jp_1930_;
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_b_1922_);
lean_dec_ref(v_database_1918_);
v_a_1945_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1941_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1941_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
v_a_1931_ = v_b_1922_;
goto v___jp_1930_;
}
}
v___jp_1930_:
{
size_t v___x_1932_; size_t v___x_1933_; 
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_add(v_i_1921_, v___x_1932_);
v_i_1921_ = v___x_1933_;
v_b_1922_ = v_a_1931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(lean_object* v_database_1953_, lean_object* v_as_1954_, lean_object* v_sz_1955_, lean_object* v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1955_);
lean_dec(v_sz_1955_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_database_1953_, v_as_1954_, v_sz_boxed_1965_, v_i_boxed_1966_, v_b_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec_ref(v_as_1954_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(lean_object* v_keys_1968_, lean_object* v_vals_1969_, lean_object* v_i_1970_, lean_object* v_k_1971_){
_start:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = lean_array_get_size(v_keys_1968_);
v___x_1973_ = lean_nat_dec_lt(v_i_1970_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec(v_i_1970_);
v___x_1974_ = lean_box(0);
return v___x_1974_;
}
else
{
lean_object* v_k_x27_1975_; uint8_t v___x_1976_; 
v_k_x27_1975_ = lean_array_fget_borrowed(v_keys_1968_, v_i_1970_);
v___x_1976_ = lean_name_eq(v_k_1971_, v_k_x27_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = lean_nat_add(v_i_1970_, v___x_1977_);
lean_dec(v_i_1970_);
v_i_1970_ = v___x_1978_;
goto _start;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_array_fget_borrowed(v_vals_1969_, v_i_1970_);
lean_dec(v_i_1970_);
lean_inc(v___x_1980_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1982_, lean_object* v_vals_1983_, lean_object* v_i_1984_, lean_object* v_k_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_keys_1982_, v_vals_1983_, v_i_1984_, v_k_1985_);
lean_dec(v_k_1985_);
lean_dec_ref(v_vals_1983_);
lean_dec_ref(v_keys_1982_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(lean_object* v_x_1987_, size_t v_x_1988_, lean_object* v_x_1989_){
_start:
{
if (lean_obj_tag(v_x_1987_) == 0)
{
lean_object* v_es_1990_; lean_object* v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; lean_object* v_j_1995_; lean_object* v___x_1996_; 
v_es_1990_ = lean_ctor_get(v_x_1987_, 0);
v___x_1991_ = lean_box(2);
v___x_1992_ = ((size_t)5ULL);
v___x_1993_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1);
v___x_1994_ = lean_usize_land(v_x_1988_, v___x_1993_);
v_j_1995_ = lean_usize_to_nat(v___x_1994_);
v___x_1996_ = lean_array_get_borrowed(v___x_1991_, v_es_1990_, v_j_1995_);
lean_dec(v_j_1995_);
switch(lean_obj_tag(v___x_1996_))
{
case 0:
{
lean_object* v_key_1997_; lean_object* v_val_1998_; uint8_t v___x_1999_; 
v_key_1997_ = lean_ctor_get(v___x_1996_, 0);
v_val_1998_ = lean_ctor_get(v___x_1996_, 1);
v___x_1999_ = lean_name_eq(v_x_1989_, v_key_1997_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_box(0);
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; 
lean_inc(v_val_1998_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_val_1998_);
return v___x_2001_;
}
}
case 1:
{
lean_object* v_node_2002_; size_t v___x_2003_; 
v_node_2002_ = lean_ctor_get(v___x_1996_, 0);
v___x_2003_ = lean_usize_shift_right(v_x_1988_, v___x_1992_);
v_x_1987_ = v_node_2002_;
v_x_1988_ = v___x_2003_;
goto _start;
}
default: 
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_box(0);
return v___x_2005_;
}
}
}
else
{
lean_object* v_ks_2006_; lean_object* v_vs_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_ks_2006_ = lean_ctor_get(v_x_1987_, 0);
v_vs_2007_ = lean_ctor_get(v_x_1987_, 1);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_ks_2006_, v_vs_2007_, v___x_2008_, v_x_1989_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg___boxed(lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_){
_start:
{
size_t v_x_29455__boxed_2013_; lean_object* v_res_2014_; 
v_x_29455__boxed_2013_ = lean_unbox_usize(v_x_2011_);
lean_dec(v_x_2011_);
v_res_2014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2010_, v_x_29455__boxed_2013_, v_x_2012_);
lean_dec(v_x_2012_);
lean_dec_ref(v_x_2010_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
uint64_t v___y_2018_; 
if (lean_obj_tag(v_x_2016_) == 0)
{
uint64_t v___x_2021_; 
v___x_2021_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0);
v___y_2018_ = v___x_2021_;
goto v___jp_2017_;
}
else
{
uint64_t v_hash_2022_; 
v_hash_2022_ = lean_ctor_get_uint64(v_x_2016_, sizeof(void*)*2);
v___y_2018_ = v_hash_2022_;
goto v___jp_2017_;
}
v___jp_2017_:
{
size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_uint64_to_usize(v___y_2018_);
v___x_2020_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2015_, v___x_2019_, v_x_2016_);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg___boxed(lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2023_, v_x_2024_);
lean_dec(v_x_2024_);
lean_dec_ref(v_x_2023_);
return v_res_2025_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(lean_object* v_a_2032_, lean_object* v_as_2033_, size_t v_sz_2034_, size_t v_i_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_snd_2045_; uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec(v_a_2032_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_b_2036_);
return v___x_2050_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_a_2051_ = lean_array_uget_borrowed(v_as_2033_, v_i_2035_);
v___x_2052_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_2051_);
v___x_2053_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_a_2051_, v___x_2052_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
if (lean_obj_tag(v_a_2054_) == 1)
{
lean_object* v_val_2055_; lean_object* v_pattern_2056_; lean_object* v___x_2057_; 
v_val_2055_ = lean_ctor_get(v_a_2054_, 0);
lean_inc(v_val_2055_);
lean_dec_ref(v_a_2054_);
v_pattern_2056_ = lean_ctor_get(v_val_2055_, 0);
lean_inc_ref(v_pattern_2056_);
v___x_2057_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(v_b_2036_, v_pattern_2056_, v_val_2055_);
v_snd_2045_ = v___x_2057_;
goto v___jp_2044_;
}
else
{
lean_dec(v_a_2054_);
v_snd_2045_ = v_b_2036_;
goto v___jp_2044_;
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2095_; 
v_a_2058_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2060_ = v___x_2053_;
v_isShared_2061_ = v_isSharedCheck_2095_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2053_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2095_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint8_t v___y_2063_; uint8_t v___x_2093_; 
v___x_2093_ = l_Lean_Exception_isInterrupt(v_a_2058_);
if (v___x_2093_ == 0)
{
uint8_t v___x_2094_; 
lean_inc(v_a_2058_);
v___x_2094_ = l_Lean_Exception_isRuntime(v_a_2058_);
v___y_2063_ = v___x_2094_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v___x_2093_;
goto v___jp_2062_;
}
v___jp_2062_:
{
if (v___y_2063_ == 0)
{
lean_object* v_options_2064_; uint8_t v_hasTrace_2065_; 
lean_del_object(v___x_2060_);
v_options_2064_ = lean_ctor_get(v___y_2041_, 2);
v_hasTrace_2065_ = lean_ctor_get_uint8(v_options_2064_, sizeof(void*)*1);
if (v_hasTrace_2065_ == 0)
{
lean_dec(v_a_2058_);
v_snd_2045_ = v_b_2036_;
goto v___jp_2044_;
}
else
{
lean_object* v_inheritedTraceOptions_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_inheritedTraceOptions_2066_ = lean_ctor_get(v___y_2041_, 13);
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_2068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_2069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2066_, v_options_2064_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec(v_a_2058_);
v_snd_2045_ = v_b_2036_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2070_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1);
lean_inc(v_a_2032_);
v___x_2071_ = l_Lean_MessageData_ofName(v_a_2032_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
lean_inc(v_a_2051_);
v___x_2075_ = l_Lean_MessageData_ofName(v_a_2051_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = l_Lean_Exception_toMessageData(v_a_2058_);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_2067_, v___x_2080_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_dec_ref(v___x_2081_);
v_snd_2045_ = v_b_2036_;
goto v___jp_2044_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_b_2036_);
lean_dec(v_a_2032_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
else
{
lean_object* v___x_2091_; 
lean_dec_ref(v_b_2036_);
lean_dec(v_a_2032_);
if (v_isShared_2061_ == 0)
{
v___x_2091_ = v___x_2060_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2058_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
v___jp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2035_, v___x_2046_);
v_i_2035_ = v___x_2047_;
v_b_2036_ = v_snd_2045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___boxed(lean_object* v_a_2096_, lean_object* v_as_2097_, lean_object* v_sz_2098_, lean_object* v_i_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
size_t v_sz_boxed_2108_; size_t v_i_boxed_2109_; lean_object* v_res_2110_; 
v_sz_boxed_2108_ = lean_unbox_usize(v_sz_2098_);
lean_dec(v_sz_2098_);
v_i_boxed_2109_ = lean_unbox_usize(v_i_2099_);
lean_dec(v_i_2099_);
v_res_2110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_a_2096_, v_as_2097_, v_sz_boxed_2108_, v_i_boxed_2109_, v_b_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_as_2097_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(lean_object* v_simpThms_2111_, lean_object* v_as_x27_2112_, lean_object* v_b_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
if (lean_obj_tag(v_as_x27_2112_) == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_b_2113_);
return v___x_2121_;
}
else
{
lean_object* v_head_2122_; lean_object* v_tail_2123_; lean_object* v_eqThms_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v_erased_2137_; lean_object* v_toUnfoldThms_2138_; uint8_t v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_head_2122_ = lean_ctor_get(v_as_x27_2112_, 0);
v_tail_2123_ = lean_ctor_get(v_as_x27_2112_, 1);
v_erased_2137_ = lean_ctor_get(v_simpThms_2111_, 4);
v_toUnfoldThms_2138_ = lean_ctor_get(v_simpThms_2111_, 5);
v___x_2139_ = 1;
v___x_2140_ = 0;
lean_inc(v_head_2122_);
v___x_2141_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2141_, 0, v_head_2122_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1 + 1, v___x_2140_);
v___x_2142_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_erased_2137_, v___x_2141_);
lean_dec_ref(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_toUnfoldThms_2138_, v_head_2122_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; 
lean_inc(v_head_2122_);
v___x_2144_ = l_Lean_Meta_getEqnsFor_x3f(v_head_2122_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
if (lean_obj_tag(v_a_2145_) == 1)
{
lean_object* v_val_2146_; 
v_val_2146_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref(v_a_2145_);
v_eqThms_2125_ = v_val_2146_;
v___y_2126_ = v___y_2114_;
v___y_2127_ = v___y_2115_;
v___y_2128_ = v___y_2116_;
v___y_2129_ = v___y_2117_;
v___y_2130_ = v___y_2118_;
v___y_2131_ = v___y_2119_;
goto v___jp_2124_;
}
else
{
lean_dec(v_a_2145_);
v_as_x27_2112_ = v_tail_2123_;
goto _start;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_b_2113_);
v_a_2148_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2144_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_val_2156_; 
v_val_2156_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_val_2156_);
lean_dec_ref(v___x_2143_);
v_eqThms_2125_ = v_val_2156_;
v___y_2126_ = v___y_2114_;
v___y_2127_ = v___y_2115_;
v___y_2128_ = v___y_2116_;
v___y_2129_ = v___y_2117_;
v___y_2130_ = v___y_2118_;
v___y_2131_ = v___y_2119_;
goto v___jp_2124_;
}
}
else
{
v_as_x27_2112_ = v_tail_2123_;
goto _start;
}
v___jp_2124_:
{
size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v_sz_2132_ = lean_array_size(v_eqThms_2125_);
v___x_2133_ = ((size_t)0ULL);
lean_inc(v_head_2122_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_head_2122_, v_eqThms_2125_, v_sz_2132_, v___x_2133_, v_b_2113_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec_ref(v_eqThms_2125_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v_as_x27_2112_ = v_tail_2123_;
v_b_2113_ = v_a_2135_;
goto _start;
}
else
{
return v___x_2134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg___boxed(lean_object* v_simpThms_2158_, lean_object* v_as_x27_2159_, lean_object* v_b_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2158_, v_as_x27_2159_, v_b_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v_as_x27_2159_);
lean_dec_ref(v_simpThms_2158_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(lean_object* v_database_2177_, lean_object* v_simpThms_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_specs_2186_; lean_object* v_erased_2187_; lean_object* v___f_2188_; lean_object* v_specs_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; size_t v_sz_2192_; size_t v___x_2193_; lean_object* v___x_2194_; 
v_specs_2186_ = lean_ctor_get(v_database_2177_, 0);
v_erased_2187_ = lean_ctor_get(v_database_2177_, 1);
lean_inc_ref(v_erased_2187_);
v___f_2188_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1));
v_specs_2189_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0);
v___x_2190_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2));
v___x_2191_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2188_, v_specs_2186_, v___x_2190_);
v_sz_2192_ = lean_array_size(v___x_2191_);
v___x_2193_ = ((size_t)0ULL);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_database_2177_, v___x_2191_, v_sz_2192_, v___x_2193_, v_specs_2189_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v___x_2191_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_post_2196_; lean_object* v_toUnfold_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; size_t v_sz_2200_; lean_object* v___x_2201_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
v_post_2196_ = lean_ctor_get(v_simpThms_2178_, 1);
v_toUnfold_2197_ = lean_ctor_get(v_simpThms_2178_, 3);
v___f_2198_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4));
v___x_2199_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2198_, v_post_2196_, v___x_2190_);
v_sz_2200_ = lean_array_size(v___x_2199_);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_simpThms_2178_, v___x_2199_, v_sz_2200_, v___x_2193_, v_a_2195_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v___x_2199_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_toUnfold_2197_);
v___x_2204_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2178_, v___x_2203_, v_a_2202_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v___x_2203_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2205_);
lean_ctor_set(v___x_2209_, 1, v_erased_2187_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v_erased_2187_);
v_a_2214_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2204_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2204_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v_erased_2187_);
v_a_2222_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2201_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2201_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_erased_2187_);
v_a_2230_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2194_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2194_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object* v_database_2238_, lean_object* v_simpThms_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(v_database_2238_, v_simpThms_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec_ref(v_simpThms_2239_);
return v_res_2247_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(lean_object* v_00_u03b2_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_x_2249_, v_x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___boxed(lean_object* v_00_u03b2_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
uint8_t v_res_2255_; lean_object* v_r_2256_; 
v_res_2255_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_00_u03b2_2252_, v_x_2253_, v_x_2254_);
lean_dec_ref(v_x_2254_);
lean_dec_ref(v_x_2253_);
v_r_2256_ = lean_box(v_res_2255_);
return v_r_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(lean_object* v_cls_2257_, lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_2257_, v_msg_2258_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___boxed(lean_object* v_cls_2267_, lean_object* v_msg_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(v_cls_2267_, v_msg_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(lean_object* v_00_u03b2_2277_, lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2278_, v_x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___boxed(lean_object* v_00_u03b2_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(v_00_u03b2_2281_, v_x_2282_, v_x_2283_);
lean_dec(v_x_2283_);
lean_dec_ref(v_x_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(lean_object* v_00_u03c3_2285_, lean_object* v_00_u03b1_2286_, lean_object* v_f_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_2287_, v_x_2288_, v_x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___boxed(lean_object* v_00_u03c3_2291_, lean_object* v_00_u03b1_2292_, lean_object* v_f_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(v_00_u03c3_2291_, v_00_u03b1_2292_, v_f_2293_, v_x_2294_, v_x_2295_);
lean_dec_ref(v_x_2295_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(lean_object* v_map_2297_, lean_object* v_f_2298_, lean_object* v_init_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2298_, v_map_2297_, v_init_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg___boxed(lean_object* v_map_2301_, lean_object* v_f_2302_, lean_object* v_init_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(v_map_2301_, v_f_2302_, v_init_2303_);
lean_dec_ref(v_map_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(lean_object* v_00_u03c3_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_map_2307_, lean_object* v_f_2308_, lean_object* v_init_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2308_, v_map_2307_, v_init_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___boxed(lean_object* v_00_u03c3_2311_, lean_object* v_00_u03b2_2312_, lean_object* v_map_2313_, lean_object* v_f_2314_, lean_object* v_init_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(v_00_u03c3_2311_, v_00_u03b2_2312_, v_map_2313_, v_f_2314_, v_init_2315_);
lean_dec_ref(v_map_2313_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(lean_object* v_simpThms_2317_, lean_object* v_as_2318_, lean_object* v_as_x27_2319_, lean_object* v_b_2320_, lean_object* v_a_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2317_, v_as_x27_2319_, v_b_2320_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___boxed(lean_object* v_simpThms_2330_, lean_object* v_as_2331_, lean_object* v_as_x27_2332_, lean_object* v_b_2333_, lean_object* v_a_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(v_simpThms_2330_, v_as_2331_, v_as_x27_2332_, v_b_2333_, v_a_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v_as_x27_2332_);
lean_dec(v_as_2331_);
lean_dec_ref(v_simpThms_2330_);
return v_res_2342_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, size_t v_x_2345_, lean_object* v_x_2346_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(v_x_2344_, v_x_2345_, v_x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_){
_start:
{
size_t v_x_29955__boxed_2352_; uint8_t v_res_2353_; lean_object* v_r_2354_; 
v_x_29955__boxed_2352_ = lean_unbox_usize(v_x_2350_);
lean_dec(v_x_2350_);
v_res_2353_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_00_u03b2_2348_, v_x_2349_, v_x_29955__boxed_2352_, v_x_2351_);
lean_dec_ref(v_x_2351_);
lean_dec_ref(v_x_2349_);
v_r_2354_ = lean_box(v_res_2353_);
return v_r_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(lean_object* v_00_u03b2_2355_, lean_object* v_x_2356_, size_t v_x_2357_, lean_object* v_x_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2356_, v_x_2357_, v_x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_){
_start:
{
size_t v_x_29966__boxed_2364_; lean_object* v_res_2365_; 
v_x_29966__boxed_2364_ = lean_unbox_usize(v_x_2362_);
lean_dec(v_x_2362_);
v_res_2365_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(v_00_u03b2_2360_, v_x_2361_, v_x_29966__boxed_2364_, v_x_2363_);
lean_dec(v_x_2363_);
lean_dec_ref(v_x_2361_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(lean_object* v_00_u03b1_2366_, lean_object* v_00_u03c3_2367_, lean_object* v_f_2368_, lean_object* v_as_2369_, size_t v_i_2370_, size_t v_stop_2371_, lean_object* v_b_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_2368_, v_as_2369_, v_i_2370_, v_stop_2371_, v_b_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_00_u03c3_2375_, lean_object* v_f_2376_, lean_object* v_as_2377_, lean_object* v_i_2378_, lean_object* v_stop_2379_, lean_object* v_b_2380_){
_start:
{
size_t v_i_boxed_2381_; size_t v_stop_boxed_2382_; lean_object* v_res_2383_; 
v_i_boxed_2381_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_stop_boxed_2382_ = lean_unbox_usize(v_stop_2379_);
lean_dec(v_stop_2379_);
v_res_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(v_00_u03b1_2374_, v_00_u03c3_2375_, v_f_2376_, v_as_2377_, v_i_boxed_2381_, v_stop_boxed_2382_, v_b_2380_);
lean_dec_ref(v_as_2377_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(lean_object* v_00_u03b1_2384_, lean_object* v_00_u03c3_2385_, lean_object* v_f_2386_, lean_object* v_as_2387_, size_t v_i_2388_, size_t v_stop_2389_, lean_object* v_b_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_2386_, v_as_2387_, v_i_2388_, v_stop_2389_, v_b_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_00_u03c3_2393_, lean_object* v_f_2394_, lean_object* v_as_2395_, lean_object* v_i_2396_, lean_object* v_stop_2397_, lean_object* v_b_2398_){
_start:
{
size_t v_i_boxed_2399_; size_t v_stop_boxed_2400_; lean_object* v_res_2401_; 
v_i_boxed_2399_ = lean_unbox_usize(v_i_2396_);
lean_dec(v_i_2396_);
v_stop_boxed_2400_ = lean_unbox_usize(v_stop_2397_);
lean_dec(v_stop_2397_);
v_res_2401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(v_00_u03b1_2392_, v_00_u03c3_2393_, v_f_2394_, v_as_2395_, v_i_boxed_2399_, v_stop_boxed_2400_, v_b_2398_);
lean_dec_ref(v_as_2395_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(lean_object* v_00_u03c3_2402_, lean_object* v_00_u03b1_2403_, lean_object* v_00_u03b2_2404_, lean_object* v_f_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2405_, v_x_2406_, v_x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___boxed(lean_object* v_00_u03c3_2409_, lean_object* v_00_u03b1_2410_, lean_object* v_00_u03b2_2411_, lean_object* v_f_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(v_00_u03c3_2409_, v_00_u03b1_2410_, v_00_u03b2_2411_, v_f_2412_, v_x_2413_, v_x_2414_);
lean_dec_ref(v_x_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(lean_object* v_00_u03b2_2416_, lean_object* v_m_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___boxed(lean_object* v_00_u03b2_2419_, lean_object* v_m_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(v_00_u03b2_2419_, v_m_2420_);
lean_dec_ref(v_m_2420_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_x_2423_, v_x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2426_, lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(v_00_u03b2_2426_, v_x_2427_, v_x_2428_);
lean_dec(v_x_2428_);
lean_dec_ref(v_x_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_x_2431_, v_x_2432_, v_x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2435_, lean_object* v_keys_2436_, lean_object* v_vals_2437_, lean_object* v_heq_2438_, lean_object* v_i_2439_, lean_object* v_k_2440_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg(v_keys_2436_, v_i_2439_, v_k_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2442_, lean_object* v_keys_2443_, lean_object* v_vals_2444_, lean_object* v_heq_2445_, lean_object* v_i_2446_, lean_object* v_k_2447_){
_start:
{
uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_res_2448_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_00_u03b2_2442_, v_keys_2443_, v_vals_2444_, v_heq_2445_, v_i_2446_, v_k_2447_);
lean_dec_ref(v_k_2447_);
lean_dec_ref(v_vals_2444_);
lean_dec_ref(v_keys_2443_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(lean_object* v_00_u03b2_2450_, lean_object* v_keys_2451_, lean_object* v_vals_2452_, lean_object* v_heq_2453_, lean_object* v_i_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_keys_2451_, v_vals_2452_, v_i_2454_, v_k_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2457_, lean_object* v_keys_2458_, lean_object* v_vals_2459_, lean_object* v_heq_2460_, lean_object* v_i_2461_, lean_object* v_k_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(v_00_u03b2_2457_, v_keys_2458_, v_vals_2459_, v_heq_2460_, v_i_2461_, v_k_2462_);
lean_dec(v_k_2462_);
lean_dec_ref(v_vals_2459_);
lean_dec_ref(v_keys_2458_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(lean_object* v_00_u03b1_2464_, lean_object* v_00_u03b2_2465_, lean_object* v_00_u03c3_2466_, lean_object* v_f_2467_, lean_object* v_as_2468_, size_t v_i_2469_, size_t v_stop_2470_, lean_object* v_b_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_2467_, v_as_2468_, v_i_2469_, v_stop_2470_, v_b_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___boxed(lean_object* v_00_u03b1_2473_, lean_object* v_00_u03b2_2474_, lean_object* v_00_u03c3_2475_, lean_object* v_f_2476_, lean_object* v_as_2477_, lean_object* v_i_2478_, lean_object* v_stop_2479_, lean_object* v_b_2480_){
_start:
{
size_t v_i_boxed_2481_; size_t v_stop_boxed_2482_; lean_object* v_res_2483_; 
v_i_boxed_2481_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_stop_boxed_2482_ = lean_unbox_usize(v_stop_2479_);
lean_dec(v_stop_2479_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(v_00_u03b1_2473_, v_00_u03b2_2474_, v_00_u03c3_2475_, v_f_2476_, v_as_2477_, v_i_boxed_2481_, v_stop_boxed_2482_, v_b_2480_);
lean_dec_ref(v_as_2477_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object* v_00_u03c3_2484_, lean_object* v_00_u03b1_2485_, lean_object* v_00_u03b2_2486_, lean_object* v_f_2487_, lean_object* v_keys_2488_, lean_object* v_vals_2489_, lean_object* v_heq_2490_, lean_object* v_i_2491_, lean_object* v_acc_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_2487_, v_keys_2488_, v_vals_2489_, v_i_2491_, v_acc_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object* v_00_u03c3_2494_, lean_object* v_00_u03b1_2495_, lean_object* v_00_u03b2_2496_, lean_object* v_f_2497_, lean_object* v_keys_2498_, lean_object* v_vals_2499_, lean_object* v_heq_2500_, lean_object* v_i_2501_, lean_object* v_acc_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(v_00_u03c3_2494_, v_00_u03b1_2495_, v_00_u03b2_2496_, v_f_2497_, v_keys_2498_, v_vals_2499_, v_heq_2500_, v_i_2501_, v_acc_2502_);
lean_dec_ref(v_vals_2499_);
lean_dec_ref(v_keys_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(lean_object* v_00_u03c3_2504_, lean_object* v_00_u03b2_2505_, lean_object* v_map_2506_, lean_object* v_f_2507_, lean_object* v_init_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_map_2506_, v_f_2507_, v_init_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___boxed(lean_object* v_00_u03c3_2510_, lean_object* v_00_u03b2_2511_, lean_object* v_map_2512_, lean_object* v_f_2513_, lean_object* v_init_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(v_00_u03c3_2510_, v_00_u03b2_2511_, v_map_2512_, v_f_2513_, v_init_2514_);
lean_dec_ref(v_map_2512_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b2_2516_, lean_object* v_x_2517_, size_t v_x_2518_, lean_object* v_x_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(v_x_2517_, v_x_2518_, v_x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b2_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
size_t v_x_30017__boxed_2525_; lean_object* v_res_2526_; 
v_x_30017__boxed_2525_ = lean_unbox_usize(v_x_2523_);
lean_dec(v_x_2523_);
v_res_2526_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12(v_00_u03b2_2521_, v_x_2522_, v_x_30017__boxed_2525_, v_x_2524_);
lean_dec(v_x_2524_);
lean_dec_ref(v_x_2522_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14(lean_object* v_00_u03b2_2527_, lean_object* v_x_2528_, size_t v_x_2529_, size_t v_x_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_x_2528_, v_x_2529_, v_x_2530_, v_x_2531_, v_x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___boxed(lean_object* v_00_u03b2_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
size_t v_x_30028__boxed_2540_; size_t v_x_30029__boxed_2541_; lean_object* v_res_2542_; 
v_x_30028__boxed_2540_ = lean_unbox_usize(v_x_2536_);
lean_dec(v_x_2536_);
v_x_30029__boxed_2541_ = lean_unbox_usize(v_x_2537_);
lean_dec(v_x_2537_);
v_res_2542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14(v_00_u03b2_2534_, v_x_2535_, v_x_30028__boxed_2540_, v_x_30029__boxed_2541_, v_x_2538_, v_x_2539_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg(lean_object* v_map_2543_, lean_object* v_f_2544_, lean_object* v_init_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2544_, v_map_2543_, v_init_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg___boxed(lean_object* v_map_2547_, lean_object* v_f_2548_, lean_object* v_init_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg(v_map_2547_, v_f_2548_, v_init_2549_);
lean_dec_ref(v_map_2547_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30(lean_object* v_00_u03c3_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_map_2553_, lean_object* v_f_2554_, lean_object* v_init_2555_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2554_, v_map_2553_, v_init_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___boxed(lean_object* v_00_u03c3_2557_, lean_object* v_00_u03b2_2558_, lean_object* v_map_2559_, lean_object* v_f_2560_, lean_object* v_init_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30(v_00_u03c3_2557_, v_00_u03b2_2558_, v_map_2559_, v_f_2560_, v_init_2561_);
lean_dec_ref(v_map_2559_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21(lean_object* v_00_u03b2_2563_, lean_object* v_keys_2564_, lean_object* v_vals_2565_, lean_object* v_heq_2566_, lean_object* v_i_2567_, lean_object* v_k_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg(v_keys_2564_, v_vals_2565_, v_i_2567_, v_k_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___boxed(lean_object* v_00_u03b2_2570_, lean_object* v_keys_2571_, lean_object* v_vals_2572_, lean_object* v_heq_2573_, lean_object* v_i_2574_, lean_object* v_k_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21(v_00_u03b2_2570_, v_keys_2571_, v_vals_2572_, v_heq_2573_, v_i_2574_, v_k_2575_);
lean_dec(v_k_2575_);
lean_dec_ref(v_vals_2572_);
lean_dec_ref(v_keys_2571_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24(lean_object* v_00_u03b2_2577_, lean_object* v_n_2578_, lean_object* v_k_2579_, lean_object* v_v_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24___redArg(v_n_2578_, v_k_2579_, v_v_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25(lean_object* v_00_u03b2_2582_, size_t v_depth_2583_, lean_object* v_keys_2584_, lean_object* v_vals_2585_, lean_object* v_heq_2586_, lean_object* v_i_2587_, lean_object* v_entries_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg(v_depth_2583_, v_keys_2584_, v_vals_2585_, v_i_2587_, v_entries_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___boxed(lean_object* v_00_u03b2_2590_, lean_object* v_depth_2591_, lean_object* v_keys_2592_, lean_object* v_vals_2593_, lean_object* v_heq_2594_, lean_object* v_i_2595_, lean_object* v_entries_2596_){
_start:
{
size_t v_depth_boxed_2597_; lean_object* v_res_2598_; 
v_depth_boxed_2597_ = lean_unbox_usize(v_depth_2591_);
lean_dec(v_depth_2591_);
v_res_2598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25(v_00_u03b2_2590_, v_depth_boxed_2597_, v_keys_2592_, v_vals_2593_, v_heq_2594_, v_i_2595_, v_entries_2596_);
lean_dec_ref(v_vals_2593_);
lean_dec_ref(v_keys_2592_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30(lean_object* v_x_2599_, lean_object* v_keys_2600_, lean_object* v_v_2601_, lean_object* v_k_2602_, lean_object* v_as_2603_, lean_object* v_k_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg(v_x_2599_, v_keys_2600_, v_v_2601_, v_k_2602_, v_as_2603_, v_k_2604_, v_x_2605_, v_x_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___boxed(lean_object* v_x_2610_, lean_object* v_keys_2611_, lean_object* v_v_2612_, lean_object* v_k_2613_, lean_object* v_as_2614_, lean_object* v_k_2615_, lean_object* v_x_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30(v_x_2610_, v_keys_2611_, v_v_2612_, v_k_2613_, v_as_2614_, v_k_2615_, v_x_2616_, v_x_2617_, v_x_2618_, v_x_2619_);
lean_dec_ref(v_k_2615_);
lean_dec_ref(v_keys_2611_);
lean_dec(v_x_2610_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31(lean_object* v_00_u03b2_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31___redArg(v_x_2622_, v_x_2623_, v_x_2624_, v_x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(lean_object* v_xs_2627_, lean_object* v_j_2628_){
_start:
{
lean_object* v_zero_2629_; uint8_t v_isZero_2630_; 
v_zero_2629_ = lean_unsigned_to_nat(0u);
v_isZero_2630_ = lean_nat_dec_eq(v_j_2628_, v_zero_2629_);
if (v_isZero_2630_ == 1)
{
lean_dec(v_j_2628_);
return v_xs_2627_;
}
else
{
lean_object* v_one_2631_; lean_object* v_n_2632_; lean_object* v___x_2633_; lean_object* v_priority_2634_; lean_object* v___x_2635_; lean_object* v_priority_2636_; uint8_t v___x_2637_; 
v_one_2631_ = lean_unsigned_to_nat(1u);
v_n_2632_ = lean_nat_sub(v_j_2628_, v_one_2631_);
v___x_2633_ = lean_array_fget_borrowed(v_xs_2627_, v_n_2632_);
v_priority_2634_ = lean_ctor_get(v___x_2633_, 3);
v___x_2635_ = lean_array_fget_borrowed(v_xs_2627_, v_j_2628_);
v_priority_2636_ = lean_ctor_get(v___x_2635_, 3);
v___x_2637_ = lean_nat_dec_lt(v_priority_2634_, v_priority_2636_);
if (v___x_2637_ == 0)
{
lean_dec(v_n_2632_);
lean_dec(v_j_2628_);
return v_xs_2627_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_array_fswap(v_xs_2627_, v_j_2628_, v_n_2632_);
lean_dec(v_j_2628_);
v_xs_2627_ = v___x_2638_;
v_j_2628_ = v_n_2632_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(lean_object* v_xs_2640_, lean_object* v_i_2641_, lean_object* v_fuel_2642_){
_start:
{
lean_object* v_zero_2643_; uint8_t v_isZero_2644_; 
v_zero_2643_ = lean_unsigned_to_nat(0u);
v_isZero_2644_ = lean_nat_dec_eq(v_fuel_2642_, v_zero_2643_);
if (v_isZero_2644_ == 1)
{
lean_dec(v_fuel_2642_);
lean_dec(v_i_2641_);
return v_xs_2640_;
}
else
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = lean_array_get_size(v_xs_2640_);
v___x_2646_ = lean_nat_dec_lt(v_i_2641_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_dec(v_fuel_2642_);
lean_dec(v_i_2641_);
return v_xs_2640_;
}
else
{
lean_object* v_one_2647_; lean_object* v_n_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_one_2647_ = lean_unsigned_to_nat(1u);
v_n_2648_ = lean_nat_sub(v_fuel_2642_, v_one_2647_);
lean_dec(v_fuel_2642_);
lean_inc(v_i_2641_);
v___x_2649_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_xs_2640_, v_i_2641_);
v___x_2650_ = lean_nat_add(v_i_2641_, v_one_2647_);
lean_dec(v_i_2641_);
v_xs_2640_ = v___x_2649_;
v_i_2641_ = v___x_2650_;
v_fuel_2642_ = v_n_2648_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(lean_object* v_a_2655_, lean_object* v_as_2656_, size_t v_sz_2657_, size_t v_i_2658_, lean_object* v_b_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_lt(v_i_2658_, v_sz_2657_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
lean_dec_ref(v_a_2655_);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_b_2659_);
return v___x_2668_;
}
else
{
lean_object* v_a_2669_; lean_object* v_pattern_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v_b_2659_);
v_a_2669_ = lean_array_uget_borrowed(v_as_2656_, v_i_2658_);
v_pattern_2670_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_a_2655_);
lean_inc_ref(v_pattern_2670_);
v___x_2671_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_2670_, v_a_2655_, v___x_2667_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2694_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2694_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2694_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_box(0);
if (lean_obj_tag(v_a_2672_) == 1)
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v_a_2655_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_a_2672_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_a_2672_, 0);
lean_dec(v_unused_2689_);
v___x_2678_ = v_a_2672_;
v_isShared_2679_ = v_isSharedCheck_2688_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v_a_2672_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2688_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_inc(v_a_2669_);
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_a_2669_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___x_2676_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2683_);
v___x_2685_ = v___x_2674_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; 
lean_del_object(v___x_2674_);
lean_dec(v_a_2672_);
v___x_2690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0));
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_add(v_i_2658_, v___x_2691_);
v_i_2658_ = v___x_2692_;
v_b_2659_ = v___x_2690_;
goto _start;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v_a_2655_);
v_a_2695_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2671_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2671_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___boxed(lean_object* v_a_2703_, lean_object* v_as_2704_, lean_object* v_sz_2705_, lean_object* v_i_2706_, lean_object* v_b_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
size_t v_sz_boxed_2715_; size_t v_i_boxed_2716_; lean_object* v_res_2717_; 
v_sz_boxed_2715_ = lean_unbox_usize(v_sz_2705_);
lean_dec(v_sz_2705_);
v_i_boxed_2716_ = lean_unbox_usize(v_i_2706_);
lean_dec(v_i_2706_);
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v_a_2703_, v_as_2704_, v_sz_boxed_2715_, v_i_boxed_2716_, v_b_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec_ref(v_as_2704_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object* v_database_2718_, lean_object* v_e_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2789_; 
v___x_2727_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_2719_, v_a_2723_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2789_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2789_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2728_, v_a_2721_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2780_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2780_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2780_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v_specs_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v_specs_2737_ = lean_ctor_get(v_database_2718_, 0);
v___x_2738_ = l_Lean_Meta_Sym_getMatch___redArg(v_specs_2737_, v_a_2733_);
v___x_2739_ = lean_array_get_size(v___x_2738_);
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = lean_nat_dec_eq(v___x_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; size_t v_sz_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2735_);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(v___x_2738_, v___x_2742_, v___x_2739_);
v___x_2744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0));
v_sz_2745_ = lean_array_size(v___x_2743_);
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v_a_2733_, v___x_2743_, v_sz_2745_, v___x_2746_, v___x_2744_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2763_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2763_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2763_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_fst_2752_; 
v_fst_2752_ = lean_ctor_get(v_a_2748_, 0);
lean_inc(v_fst_2752_);
lean_dec(v_a_2748_);
if (lean_obj_tag(v_fst_2752_) == 0)
{
lean_object* v___x_2754_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2743_);
v___x_2754_ = v___x_2730_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2743_);
v___x_2754_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2756_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2754_);
v___x_2756_ = v___x_2750_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_val_2759_; lean_object* v___x_2761_; 
lean_dec_ref(v___x_2743_);
lean_del_object(v___x_2730_);
v_val_2759_ = lean_ctor_get(v_fst_2752_, 0);
lean_inc(v_val_2759_);
lean_dec_ref(v_fst_2752_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_val_2759_);
v___x_2761_ = v___x_2750_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_val_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec_ref(v___x_2743_);
lean_del_object(v___x_2730_);
v_a_2764_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2747_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2747_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec(v_a_2733_);
v___x_2772_ = lean_unsigned_to_nat(0u);
v___x_2773_ = lean_array_fget(v___x_2738_, v___x_2772_);
lean_dec_ref(v___x_2738_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 1);
lean_ctor_set(v___x_2730_, 0, v___x_2773_);
v___x_2775_ = v___x_2730_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2777_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2775_);
v___x_2777_ = v___x_2735_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_del_object(v___x_2730_);
v_a_2781_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2732_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2732_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(lean_object* v_database_2790_, lean_object* v_e_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(v_database_2790_, v_e_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec_ref(v_database_2790_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(lean_object* v_xs_2800_, lean_object* v_j_2801_, lean_object* v_h_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_xs_2800_, v_j_2801_);
return v___x_2803_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default);
l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew = _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
}
#ifdef __cplusplus
}
#endif
