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
lean_dec_ref_known(v___x_71_, 1);
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
lean_dec_ref_known(v_kind_101_, 1);
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
lean_dec_ref_known(v___x_102_, 1);
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
v___x_162_ = 3ULL;
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
lean_dec_ref_known(v___x_169_, 7);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v_snd_172_; lean_object* v_fst_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_233_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
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
lean_dec_ref_known(v___y_212_, 1);
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
lean_dec_ref_known(v___x_369_, 1);
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
lean_dec_ref_known(v___x_625_, 7);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_snd_628_; lean_object* v_fst_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_710_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
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
lean_dec_ref_known(v___x_637_, 1);
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
lean_dec_ref_known(v___x_747_, 1);
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
lean_dec_ref_known(v___x_754_, 1);
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
lean_dec_ref_known(v___x_758_, 1);
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
lean_dec_ref_known(v___x_768_, 1);
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
lean_dec_ref_known(v_ty_854_, 3);
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
lean_dec_ref_known(v___x_942_, 1);
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
size_t v_x_28184__boxed_1169_; uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_x_28184__boxed_1169_ = lean_unbox_usize(v_x_1167_);
lean_dec(v_x_1167_);
v_res_1170_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(v_x_1166_, v_x_28184__boxed_1169_, v_x_1168_);
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
size_t v_x_28390__boxed_1343_; size_t v_x_28391__boxed_1344_; lean_object* v_res_1345_; 
v_x_28390__boxed_1343_ = lean_unbox_usize(v_x_1339_);
lean_dec(v_x_1339_);
v_x_28391__boxed_1344_ = lean_unbox_usize(v_x_1340_);
lean_dec(v_x_1340_);
v_res_1345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_x_1338_, v_x_28390__boxed_1343_, v_x_28391__boxed_1344_, v_x_1341_, v_x_1342_);
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
lean_dec_ref_known(v___x_1498_, 2);
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
size_t v_x_28831__boxed_1593_; lean_object* v_res_1594_; 
v_x_28831__boxed_1593_ = lean_unbox_usize(v_x_1591_);
lean_dec(v_x_1591_);
v_res_1594_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(v_x_1590_, v_x_28831__boxed_1593_, v_x_1592_);
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
lean_dec_ref_known(v___x_1620_, 1);
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
lean_object* v_ref_1651_; lean_object* v___x_1652_; lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1697_; 
v_ref_1651_ = lean_ctor_get(v___y_1648_, 5);
v___x_1652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1697_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1697_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v_traceState_1658_; lean_object* v_env_1659_; lean_object* v_nextMacroScope_1660_; lean_object* v_ngen_1661_; lean_object* v_auxDeclNGen_1662_; lean_object* v_cache_1663_; lean_object* v_messages_1664_; lean_object* v_infoState_1665_; lean_object* v_snapshotTasks_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1696_; 
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
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1668_ = v___x_1657_;
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
else
{
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
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint64_t v_tid_1670_; lean_object* v_traces_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1695_; 
v_tid_1670_ = lean_ctor_get_uint64(v_traceState_1658_, sizeof(void*)*1);
v_traces_1671_ = lean_ctor_get(v_traceState_1658_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_traceState_1658_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1673_ = v_traceState_1658_;
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_traces_1671_);
lean_dec(v_traceState_1658_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1695_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; double v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1675_ = lean_box(0);
v___x_1676_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0);
v___x_1677_ = 0;
v___x_1678_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1));
v___x_1679_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1679_, 0, v_cls_1644_);
lean_ctor_set(v___x_1679_, 1, v___x_1675_);
lean_ctor_set(v___x_1679_, 2, v___x_1678_);
lean_ctor_set_float(v___x_1679_, sizeof(void*)*3, v___x_1676_);
lean_ctor_set_float(v___x_1679_, sizeof(void*)*3 + 8, v___x_1676_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*3 + 16, v___x_1677_);
v___x_1680_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2));
v___x_1681_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v_a_1653_);
lean_ctor_set(v___x_1681_, 2, v___x_1680_);
lean_inc(v_ref_1651_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_ref_1651_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_PersistentArray_push___redArg(v_traces_1671_, v___x_1682_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1683_);
v___x_1685_ = v___x_1673_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1683_);
lean_ctor_set_uint64(v_reuseFailAlloc_1694_, sizeof(void*)*1, v_tid_1670_);
v___x_1685_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 4, v___x_1685_);
v___x_1687_ = v___x_1668_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_env_1659_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_nextMacroScope_1660_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_ngen_1661_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_auxDeclNGen_1662_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_cache_1663_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_messages_1664_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_infoState_1665_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_snapshotTasks_1666_);
v___x_1687_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1688_ = lean_st_ref_set(v___y_1649_, v___x_1687_);
v___x_1689_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1689_);
v___x_1691_ = v___x_1655_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___boxed(lean_object* v_cls_1698_, lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_1698_, v_msg_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1705_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5));
v___x_1719_ = l_Lean_Name_append(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7));
v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
return v___x_1722_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(lean_object* v_simpThms_1726_, lean_object* v_as_1727_, size_t v_sz_1728_, size_t v_i_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_a_1739_; uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1729_, v_sz_1728_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1730_);
return v___x_1744_;
}
else
{
lean_object* v_a_1745_; lean_object* v_origin_1746_; 
v_a_1745_ = lean_array_uget_borrowed(v_as_1727_, v_i_1729_);
v_origin_1746_ = lean_ctor_get(v_a_1745_, 4);
if (lean_obj_tag(v_origin_1746_) == 0)
{
lean_object* v_priority_1747_; lean_object* v_declName_1748_; lean_object* v_erased_1749_; uint8_t v___x_1750_; 
v_priority_1747_ = lean_ctor_get(v_a_1745_, 3);
v_declName_1748_ = lean_ctor_get(v_origin_1746_, 0);
v_erased_1749_ = lean_ctor_get(v_simpThms_1726_, 4);
v___x_1750_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_erased_1749_, v_origin_1746_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_inc(v_priority_1747_);
lean_inc(v_declName_1748_);
v___x_1751_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_declName_1748_, v_priority_1747_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
if (lean_obj_tag(v_a_1752_) == 1)
{
lean_object* v_val_1753_; lean_object* v_pattern_1754_; lean_object* v___x_1755_; 
v_val_1753_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_val_1753_);
lean_dec_ref_known(v_a_1752_, 1);
v_pattern_1754_ = lean_ctor_get(v_val_1753_, 0);
lean_inc_ref(v_pattern_1754_);
v___x_1755_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(v_b_1730_, v_pattern_1754_, v_val_1753_);
v_a_1739_ = v___x_1755_;
goto v___jp_1738_;
}
else
{
lean_dec(v_a_1752_);
v_a_1739_ = v_b_1730_;
goto v___jp_1738_;
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1789_; 
v_a_1756_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1758_ = v___x_1751_;
v_isShared_1759_ = v_isSharedCheck_1789_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1751_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1789_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
uint8_t v___y_1761_; uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_Exception_isInterrupt(v_a_1756_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
lean_inc(v_a_1756_);
v___x_1788_ = l_Lean_Exception_isRuntime(v_a_1756_);
v___y_1761_ = v___x_1788_;
goto v___jp_1760_;
}
else
{
v___y_1761_ = v___x_1787_;
goto v___jp_1760_;
}
v___jp_1760_:
{
if (v___y_1761_ == 0)
{
lean_object* v_options_1762_; uint8_t v_hasTrace_1763_; 
lean_del_object(v___x_1758_);
v_options_1762_ = lean_ctor_get(v___y_1735_, 2);
v_hasTrace_1763_ = lean_ctor_get_uint8(v_options_1762_, sizeof(void*)*1);
if (v_hasTrace_1763_ == 0)
{
lean_dec(v_a_1756_);
v_a_1739_ = v_b_1730_;
goto v___jp_1738_;
}
else
{
lean_object* v_inheritedTraceOptions_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_inheritedTraceOptions_1764_ = lean_ctor_get(v___y_1735_, 13);
v___x_1765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1766_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_1767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1764_, v_options_1762_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_dec(v_a_1756_);
v_a_1739_ = v_b_1730_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8);
lean_inc(v_declName_1748_);
v___x_1769_ = l_Lean_MessageData_ofName(v_declName_1748_);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Exception_toMessageData(v_a_1756_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_1765_, v___x_1774_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_dec_ref_known(v___x_1775_, 1);
v_a_1739_ = v_b_1730_;
goto v___jp_1738_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_b_1730_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref(v_b_1730_);
if (v_isShared_1759_ == 0)
{
v___x_1785_ = v___x_1758_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1756_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
else
{
v_a_1739_ = v_b_1730_;
goto v___jp_1738_;
}
}
else
{
v_a_1739_ = v_b_1730_;
goto v___jp_1738_;
}
}
v___jp_1738_:
{
size_t v___x_1740_; size_t v___x_1741_; 
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1729_, v___x_1740_);
v_i_1729_ = v___x_1741_;
v_b_1730_ = v_a_1739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(lean_object* v_simpThms_1790_, lean_object* v_as_1791_, lean_object* v_sz_1792_, lean_object* v_i_1793_, lean_object* v_b_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1792_);
lean_dec(v_sz_1792_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1793_);
lean_dec(v_i_1793_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_simpThms_1790_, v_as_1791_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec_ref(v_as_1791_);
lean_dec_ref(v_simpThms_1790_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
if (lean_obj_tag(v_a_1805_) == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = l_List_reverse___redArg(v_a_1806_);
return v___x_1807_;
}
else
{
lean_object* v_head_1808_; lean_object* v_tail_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
v_head_1808_ = lean_ctor_get(v_a_1805_, 0);
v_tail_1809_ = lean_ctor_get(v_a_1805_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_a_1805_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1811_ = v_a_1805_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_tail_1809_);
lean_inc(v_head_1808_);
lean_dec(v_a_1805_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_fst_1813_; lean_object* v___x_1815_; 
v_fst_1813_ = lean_ctor_get(v_head_1808_, 0);
lean_inc(v_fst_1813_);
lean_dec(v_head_1808_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v_a_1806_);
lean_ctor_set(v___x_1811_, 0, v_fst_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_fst_1813_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1806_);
v___x_1815_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
v_a_1805_ = v_tail_1809_;
v_a_1806_ = v___x_1815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0(lean_object* v_f_1819_, lean_object* v_x1_1820_, lean_object* v_x2_1821_, lean_object* v_x3_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_apply_3(v_f_1819_, v_x1_1820_, v_x2_1821_, v_x3_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(lean_object* v_f_1824_, lean_object* v_keys_1825_, lean_object* v_vals_1826_, lean_object* v_i_1827_, lean_object* v_acc_1828_){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_array_get_size(v_keys_1825_);
v___x_1830_ = lean_nat_dec_lt(v_i_1827_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_dec(v_i_1827_);
lean_dec(v_f_1824_);
return v_acc_1828_;
}
else
{
lean_object* v_k_1831_; lean_object* v_v_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_k_1831_ = lean_array_fget_borrowed(v_keys_1825_, v_i_1827_);
v_v_1832_ = lean_array_fget_borrowed(v_vals_1826_, v_i_1827_);
lean_inc(v_f_1824_);
lean_inc(v_v_1832_);
lean_inc(v_k_1831_);
v___x_1833_ = lean_apply_3(v_f_1824_, v_acc_1828_, v_k_1831_, v_v_1832_);
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_add(v_i_1827_, v___x_1834_);
lean_dec(v_i_1827_);
v_i_1827_ = v___x_1835_;
v_acc_1828_ = v___x_1833_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v_f_1837_, lean_object* v_keys_1838_, lean_object* v_vals_1839_, lean_object* v_i_1840_, lean_object* v_acc_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1837_, v_keys_1838_, v_vals_1839_, v_i_1840_, v_acc_1841_);
lean_dec_ref(v_vals_1839_);
lean_dec_ref(v_keys_1838_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(lean_object* v_f_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_object* v_es_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_es_1846_ = lean_ctor_get(v_x_1844_, 0);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_es_1846_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec(v_f_1843_);
return v_x_1845_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_le(v___x_1848_, v___x_1848_);
if (v___x_1850_ == 0)
{
if (v___x_1849_ == 0)
{
lean_dec(v_f_1843_);
return v_x_1845_;
}
else
{
size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1848_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1843_, v_es_1846_, v___x_1851_, v___x_1852_, v_x_1845_);
return v___x_1853_;
}
}
else
{
size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((size_t)0ULL);
v___x_1855_ = lean_usize_of_nat(v___x_1848_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1843_, v_es_1846_, v___x_1854_, v___x_1855_, v_x_1845_);
return v___x_1856_;
}
}
}
else
{
lean_object* v_ks_1857_; lean_object* v_vs_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_ks_1857_ = lean_ctor_get(v_x_1844_, 0);
v_vs_1858_ = lean_ctor_get(v_x_1844_, 1);
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1843_, v_ks_1857_, v_vs_1858_, v___x_1859_, v_x_1845_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(lean_object* v_f_1861_, lean_object* v_as_1862_, size_t v_i_1863_, size_t v_stop_1864_, lean_object* v_b_1865_){
_start:
{
lean_object* v___y_1867_; uint8_t v___x_1871_; 
v___x_1871_ = lean_usize_dec_eq(v_i_1863_, v_stop_1864_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_array_uget_borrowed(v_as_1862_, v_i_1863_);
switch(lean_obj_tag(v___x_1872_))
{
case 0:
{
lean_object* v_key_1873_; lean_object* v_val_1874_; lean_object* v___x_1875_; 
v_key_1873_ = lean_ctor_get(v___x_1872_, 0);
v_val_1874_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_f_1861_);
lean_inc(v_val_1874_);
lean_inc(v_key_1873_);
v___x_1875_ = lean_apply_3(v_f_1861_, v_b_1865_, v_key_1873_, v_val_1874_);
v___y_1867_ = v___x_1875_;
goto v___jp_1866_;
}
case 1:
{
lean_object* v_node_1876_; lean_object* v___x_1877_; 
v_node_1876_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_f_1861_);
v___x_1877_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_1861_, v_node_1876_, v_b_1865_);
v___y_1867_ = v___x_1877_;
goto v___jp_1866_;
}
default: 
{
v___y_1867_ = v_b_1865_;
goto v___jp_1866_;
}
}
}
else
{
lean_dec(v_f_1861_);
return v_b_1865_;
}
v___jp_1866_:
{
size_t v___x_1868_; size_t v___x_1869_; 
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_add(v_i_1863_, v___x_1868_);
v_i_1863_ = v___x_1869_;
v_b_1865_ = v___y_1867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg___boxed(lean_object* v_f_1878_, lean_object* v_as_1879_, lean_object* v_i_1880_, lean_object* v_stop_1881_, lean_object* v_b_1882_){
_start:
{
size_t v_i_boxed_1883_; size_t v_stop_boxed_1884_; lean_object* v_res_1885_; 
v_i_boxed_1883_ = lean_unbox_usize(v_i_1880_);
lean_dec(v_i_1880_);
v_stop_boxed_1884_ = lean_unbox_usize(v_stop_1881_);
lean_dec(v_stop_1881_);
v_res_1885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1878_, v_as_1879_, v_i_boxed_1883_, v_stop_boxed_1884_, v_b_1882_);
lean_dec_ref(v_as_1879_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(lean_object* v_f_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_1886_, v_x_1887_, v_x_1888_);
lean_dec_ref(v_x_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(lean_object* v_map_1890_, lean_object* v_f_1891_, lean_object* v_init_1892_){
_start:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; 
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1893_, 0, v_f_1891_);
v___x_1894_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_1893_, v_map_1890_, v_init_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___boxed(lean_object* v_map_1895_, lean_object* v_f_1896_, lean_object* v_init_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_map_1895_, v_f_1896_, v_init_1897_);
lean_dec_ref(v_map_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0(lean_object* v_ps_1899_, lean_object* v_k_1900_, lean_object* v_v_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_k_1900_);
lean_ctor_set(v___x_1902_, 1, v_v_1901_);
v___x_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_ps_1899_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(lean_object* v_m_1905_){
_start:
{
lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___f_1906_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0));
v___x_1907_ = lean_box(0);
v___x_1908_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_m_1905_, v___f_1906_, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___boxed(lean_object* v_m_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_1909_);
lean_dec_ref(v_m_1909_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(lean_object* v_s_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_s_1911_);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(v___x_1912_, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9___boxed(lean_object* v_s_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_s_1915_);
lean_dec_ref(v_s_1915_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(lean_object* v_database_1917_, lean_object* v_as_1918_, size_t v_sz_1919_, size_t v_i_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_a_1930_; uint8_t v___x_1934_; 
v___x_1934_ = lean_usize_dec_lt(v_i_1920_, v_sz_1919_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v_database_1917_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_b_1921_);
return v___x_1935_;
}
else
{
lean_object* v_a_1936_; lean_object* v_proof_1937_; lean_object* v_priority_1938_; uint8_t v___x_1939_; 
v_a_1936_ = lean_array_uget_borrowed(v_as_1918_, v_i_1920_);
v_proof_1937_ = lean_ctor_get(v_a_1936_, 2);
v_priority_1938_ = lean_ctor_get(v_a_1936_, 4);
lean_inc_ref(v_proof_1937_);
lean_inc_ref(v_database_1917_);
v___x_1939_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_database_1917_, v_proof_1937_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
lean_inc(v_priority_1938_);
lean_inc_ref(v_proof_1937_);
v___x_1940_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(v_proof_1937_, v_priority_1938_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_pattern_1942_; lean_object* v___x_1943_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v_pattern_1942_ = lean_ctor_get(v_a_1941_, 0);
lean_inc_ref(v_pattern_1942_);
v___x_1943_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(v_b_1921_, v_pattern_1942_, v_a_1941_);
v_a_1930_ = v___x_1943_;
goto v___jp_1929_;
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_b_1921_);
lean_dec_ref(v_database_1917_);
v_a_1944_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1940_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1940_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
v_a_1930_ = v_b_1921_;
goto v___jp_1929_;
}
}
v___jp_1929_:
{
size_t v___x_1931_; size_t v___x_1932_; 
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_add(v_i_1920_, v___x_1931_);
v_i_1920_ = v___x_1932_;
v_b_1921_ = v_a_1930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(lean_object* v_database_1952_, lean_object* v_as_1953_, lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
size_t v_sz_boxed_1964_; size_t v_i_boxed_1965_; lean_object* v_res_1966_; 
v_sz_boxed_1964_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1965_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_database_1952_, v_as_1953_, v_sz_boxed_1964_, v_i_boxed_1965_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec_ref(v_as_1953_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(lean_object* v_keys_1967_, lean_object* v_vals_1968_, lean_object* v_i_1969_, lean_object* v_k_1970_){
_start:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = lean_array_get_size(v_keys_1967_);
v___x_1972_ = lean_nat_dec_lt(v_i_1969_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec(v_i_1969_);
v___x_1973_ = lean_box(0);
return v___x_1973_;
}
else
{
lean_object* v_k_x27_1974_; uint8_t v___x_1975_; 
v_k_x27_1974_ = lean_array_fget_borrowed(v_keys_1967_, v_i_1969_);
v___x_1975_ = lean_name_eq(v_k_1970_, v_k_x27_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_add(v_i_1969_, v___x_1976_);
lean_dec(v_i_1969_);
v_i_1969_ = v___x_1977_;
goto _start;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_array_fget_borrowed(v_vals_1968_, v_i_1969_);
lean_dec(v_i_1969_);
lean_inc(v___x_1979_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1981_, lean_object* v_vals_1982_, lean_object* v_i_1983_, lean_object* v_k_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_keys_1981_, v_vals_1982_, v_i_1983_, v_k_1984_);
lean_dec(v_k_1984_);
lean_dec_ref(v_vals_1982_);
lean_dec_ref(v_keys_1981_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(lean_object* v_x_1986_, size_t v_x_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 0)
{
lean_object* v_es_1989_; lean_object* v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v_j_1994_; lean_object* v___x_1995_; 
v_es_1989_ = lean_ctor_get(v_x_1986_, 0);
v___x_1990_ = lean_box(2);
v___x_1991_ = ((size_t)5ULL);
v___x_1992_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg___closed__1);
v___x_1993_ = lean_usize_land(v_x_1987_, v___x_1992_);
v_j_1994_ = lean_usize_to_nat(v___x_1993_);
v___x_1995_ = lean_array_get_borrowed(v___x_1990_, v_es_1989_, v_j_1994_);
lean_dec(v_j_1994_);
switch(lean_obj_tag(v___x_1995_))
{
case 0:
{
lean_object* v_key_1996_; lean_object* v_val_1997_; uint8_t v___x_1998_; 
v_key_1996_ = lean_ctor_get(v___x_1995_, 0);
v_val_1997_ = lean_ctor_get(v___x_1995_, 1);
v___x_1998_ = lean_name_eq(v_x_1988_, v_key_1996_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_box(0);
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; 
lean_inc(v_val_1997_);
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_val_1997_);
return v___x_2000_;
}
}
case 1:
{
lean_object* v_node_2001_; size_t v___x_2002_; 
v_node_2001_ = lean_ctor_get(v___x_1995_, 0);
v___x_2002_ = lean_usize_shift_right(v_x_1987_, v___x_1991_);
v_x_1986_ = v_node_2001_;
v_x_1987_ = v___x_2002_;
goto _start;
}
default: 
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_box(0);
return v___x_2004_;
}
}
}
else
{
lean_object* v_ks_2005_; lean_object* v_vs_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_ks_2005_ = lean_ctor_get(v_x_1986_, 0);
v_vs_2006_ = lean_ctor_get(v_x_1986_, 1);
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_ks_2005_, v_vs_2006_, v___x_2007_, v_x_1988_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg___boxed(lean_object* v_x_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_){
_start:
{
size_t v_x_29429__boxed_2012_; lean_object* v_res_2013_; 
v_x_29429__boxed_2012_ = lean_unbox_usize(v_x_2010_);
lean_dec(v_x_2010_);
v_res_2013_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2009_, v_x_29429__boxed_2012_, v_x_2011_);
lean_dec(v_x_2011_);
lean_dec_ref(v_x_2009_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(lean_object* v_x_2014_, lean_object* v_x_2015_){
_start:
{
uint64_t v___y_2017_; 
if (lean_obj_tag(v_x_2015_) == 0)
{
uint64_t v___x_2020_; 
v___x_2020_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg___closed__0);
v___y_2017_ = v___x_2020_;
goto v___jp_2016_;
}
else
{
uint64_t v_hash_2021_; 
v_hash_2021_ = lean_ctor_get_uint64(v_x_2015_, sizeof(void*)*2);
v___y_2017_ = v_hash_2021_;
goto v___jp_2016_;
}
v___jp_2016_:
{
size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_uint64_to_usize(v___y_2017_);
v___x_2019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2014_, v___x_2018_, v_x_2015_);
return v___x_2019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg___boxed(lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2022_, v_x_2023_);
lean_dec(v_x_2023_);
lean_dec_ref(v_x_2022_);
return v_res_2024_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0));
v___x_2027_ = l_Lean_stringToMessageData(v___x_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2));
v___x_2030_ = l_Lean_stringToMessageData(v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(lean_object* v_a_2031_, lean_object* v_as_2032_, size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_snd_2044_; uint8_t v___x_2048_; 
v___x_2048_ = lean_usize_dec_lt(v_i_2034_, v_sz_2033_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v_a_2031_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_b_2035_);
return v___x_2049_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_a_2050_ = lean_array_uget_borrowed(v_as_2032_, v_i_2034_);
v___x_2051_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_2050_);
v___x_2052_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_a_2050_, v___x_2051_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
if (lean_obj_tag(v_a_2053_) == 1)
{
lean_object* v_val_2054_; lean_object* v_pattern_2055_; lean_object* v___x_2056_; 
v_val_2054_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_val_2054_);
lean_dec_ref_known(v_a_2053_, 1);
v_pattern_2055_ = lean_ctor_get(v_val_2054_, 0);
lean_inc_ref(v_pattern_2055_);
v___x_2056_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(v_b_2035_, v_pattern_2055_, v_val_2054_);
v_snd_2044_ = v___x_2056_;
goto v___jp_2043_;
}
else
{
lean_dec(v_a_2053_);
v_snd_2044_ = v_b_2035_;
goto v___jp_2043_;
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2094_; 
v_a_2057_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2059_ = v___x_2052_;
v_isShared_2060_ = v_isSharedCheck_2094_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2052_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2094_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
uint8_t v___y_2062_; uint8_t v___x_2092_; 
v___x_2092_ = l_Lean_Exception_isInterrupt(v_a_2057_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
lean_inc(v_a_2057_);
v___x_2093_ = l_Lean_Exception_isRuntime(v_a_2057_);
v___y_2062_ = v___x_2093_;
goto v___jp_2061_;
}
else
{
v___y_2062_ = v___x_2092_;
goto v___jp_2061_;
}
v___jp_2061_:
{
if (v___y_2062_ == 0)
{
lean_object* v_options_2063_; uint8_t v_hasTrace_2064_; 
lean_del_object(v___x_2059_);
v_options_2063_ = lean_ctor_get(v___y_2040_, 2);
v_hasTrace_2064_ = lean_ctor_get_uint8(v_options_2063_, sizeof(void*)*1);
if (v_hasTrace_2064_ == 0)
{
lean_dec(v_a_2057_);
v_snd_2044_ = v_b_2035_;
goto v___jp_2043_;
}
else
{
lean_object* v_inheritedTraceOptions_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_inheritedTraceOptions_2065_ = lean_ctor_get(v___y_2040_, 13);
v___x_2066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_2067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_2068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2065_, v_options_2063_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_dec(v_a_2057_);
v_snd_2044_ = v_b_2035_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1);
lean_inc(v_a_2031_);
v___x_2070_ = l_Lean_MessageData_ofName(v_a_2031_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
lean_inc(v_a_2050_);
v___x_2074_ = l_Lean_MessageData_ofName(v_a_2050_);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_Exception_toMessageData(v_a_2057_);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_2066_, v___x_2079_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_dec_ref_known(v___x_2080_, 1);
v_snd_2044_ = v_b_2035_;
goto v___jp_2043_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v_b_2035_);
lean_dec(v_a_2031_);
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
else
{
lean_object* v___x_2090_; 
lean_dec_ref(v_b_2035_);
lean_dec(v_a_2031_);
if (v_isShared_2060_ == 0)
{
v___x_2090_ = v___x_2059_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2057_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
}
v___jp_2043_:
{
size_t v___x_2045_; size_t v___x_2046_; 
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2034_, v___x_2045_);
v_i_2034_ = v___x_2046_;
v_b_2035_ = v_snd_2044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___boxed(lean_object* v_a_2095_, lean_object* v_as_2096_, lean_object* v_sz_2097_, lean_object* v_i_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2097_);
lean_dec(v_sz_2097_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2098_);
lean_dec(v_i_2098_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_a_2095_, v_as_2096_, v_sz_boxed_2107_, v_i_boxed_2108_, v_b_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec_ref(v_as_2096_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(lean_object* v_simpThms_2110_, lean_object* v_as_x27_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
if (lean_obj_tag(v_as_x27_2111_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_b_2112_);
return v___x_2120_;
}
else
{
lean_object* v_head_2121_; lean_object* v_tail_2122_; lean_object* v_eqThms_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v_erased_2136_; lean_object* v_toUnfoldThms_2137_; uint8_t v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_head_2121_ = lean_ctor_get(v_as_x27_2111_, 0);
v_tail_2122_ = lean_ctor_get(v_as_x27_2111_, 1);
v_erased_2136_ = lean_ctor_get(v_simpThms_2110_, 4);
v_toUnfoldThms_2137_ = lean_ctor_get(v_simpThms_2110_, 5);
v___x_2138_ = 1;
v___x_2139_ = 0;
lean_inc(v_head_2121_);
v___x_2140_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2140_, 0, v_head_2121_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*1, v___x_2138_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*1 + 1, v___x_2139_);
v___x_2141_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_erased_2136_, v___x_2140_);
lean_dec_ref_known(v___x_2140_, 1);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_toUnfoldThms_2137_, v_head_2121_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; 
lean_inc(v_head_2121_);
v___x_2143_ = l_Lean_Meta_getEqnsFor_x3f(v_head_2121_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2145_; 
v_val_2145_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_a_2144_, 1);
v_eqThms_2124_ = v_val_2145_;
v___y_2125_ = v___y_2113_;
v___y_2126_ = v___y_2114_;
v___y_2127_ = v___y_2115_;
v___y_2128_ = v___y_2116_;
v___y_2129_ = v___y_2117_;
v___y_2130_ = v___y_2118_;
goto v___jp_2123_;
}
else
{
lean_dec(v_a_2144_);
v_as_x27_2111_ = v_tail_2122_;
goto _start;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_b_2112_);
v_a_2147_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2143_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2143_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_val_2155_; 
v_val_2155_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2155_);
lean_dec_ref_known(v___x_2142_, 1);
v_eqThms_2124_ = v_val_2155_;
v___y_2125_ = v___y_2113_;
v___y_2126_ = v___y_2114_;
v___y_2127_ = v___y_2115_;
v___y_2128_ = v___y_2116_;
v___y_2129_ = v___y_2117_;
v___y_2130_ = v___y_2118_;
goto v___jp_2123_;
}
}
else
{
v_as_x27_2111_ = v_tail_2122_;
goto _start;
}
v___jp_2123_:
{
size_t v_sz_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v_sz_2131_ = lean_array_size(v_eqThms_2124_);
v___x_2132_ = ((size_t)0ULL);
lean_inc(v_head_2121_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_head_2121_, v_eqThms_2124_, v_sz_2131_, v___x_2132_, v_b_2112_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec_ref(v_eqThms_2124_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v_as_x27_2111_ = v_tail_2122_;
v_b_2112_ = v_a_2134_;
goto _start;
}
else
{
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg___boxed(lean_object* v_simpThms_2157_, lean_object* v_as_x27_2158_, lean_object* v_b_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2157_, v_as_x27_2158_, v_b_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v_as_x27_2158_);
lean_dec_ref(v_simpThms_2157_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(lean_object* v_database_2176_, lean_object* v_simpThms_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_specs_2185_; lean_object* v_erased_2186_; lean_object* v___f_2187_; lean_object* v_specs_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; size_t v_sz_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v_specs_2185_ = lean_ctor_get(v_database_2176_, 0);
v_erased_2186_ = lean_ctor_get(v_database_2176_, 1);
lean_inc_ref(v_erased_2186_);
v___f_2187_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1));
v_specs_2188_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0);
v___x_2189_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2));
v___x_2190_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2187_, v_specs_2185_, v___x_2189_);
v_sz_2191_ = lean_array_size(v___x_2190_);
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_database_2176_, v___x_2190_, v_sz_2191_, v___x_2192_, v_specs_2188_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
lean_dec(v___x_2190_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v_post_2195_; lean_object* v_toUnfold_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; size_t v_sz_2199_; lean_object* v___x_2200_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v_post_2195_ = lean_ctor_get(v_simpThms_2177_, 1);
v_toUnfold_2196_ = lean_ctor_get(v_simpThms_2177_, 3);
v___f_2197_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4));
v___x_2198_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2197_, v_post_2195_, v___x_2189_);
v_sz_2199_ = lean_array_size(v___x_2198_);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_simpThms_2177_, v___x_2198_, v_sz_2199_, v___x_2192_, v_a_2194_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
lean_dec(v___x_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_toUnfold_2196_);
v___x_2203_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2177_, v___x_2202_, v_a_2201_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
lean_dec(v___x_2202_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2204_);
lean_ctor_set(v___x_2208_, 1, v_erased_2186_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v_erased_2186_);
v_a_2213_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2203_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2203_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_erased_2186_);
v_a_2221_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2200_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2200_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_erased_2186_);
v_a_2229_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2193_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2193_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object* v_database_2237_, lean_object* v_simpThms_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(v_database_2237_, v_simpThms_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec_ref(v_simpThms_2238_);
return v_res_2246_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(lean_object* v_00_u03b2_2247_, lean_object* v_x_2248_, lean_object* v_x_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___redArg(v_x_2248_, v_x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1___boxed(lean_object* v_00_u03b2_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
uint8_t v_res_2254_; lean_object* v_r_2255_; 
v_res_2254_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_00_u03b2_2251_, v_x_2252_, v_x_2253_);
lean_dec_ref(v_x_2253_);
lean_dec_ref(v_x_2252_);
v_r_2255_ = lean_box(v_res_2254_);
return v_r_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(lean_object* v_cls_2256_, lean_object* v_msg_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_2256_, v_msg_2257_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___boxed(lean_object* v_cls_2266_, lean_object* v_msg_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(v_cls_2266_, v_msg_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(lean_object* v_00_u03b2_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2277_, v_x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___boxed(lean_object* v_00_u03b2_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(v_00_u03b2_2280_, v_x_2281_, v_x_2282_);
lean_dec(v_x_2282_);
lean_dec_ref(v_x_2281_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(lean_object* v_00_u03c3_2284_, lean_object* v_00_u03b1_2285_, lean_object* v_f_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_2286_, v_x_2287_, v_x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___boxed(lean_object* v_00_u03c3_2290_, lean_object* v_00_u03b1_2291_, lean_object* v_f_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(v_00_u03c3_2290_, v_00_u03b1_2291_, v_f_2292_, v_x_2293_, v_x_2294_);
lean_dec_ref(v_x_2294_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(lean_object* v_map_2296_, lean_object* v_f_2297_, lean_object* v_init_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2297_, v_map_2296_, v_init_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg___boxed(lean_object* v_map_2300_, lean_object* v_f_2301_, lean_object* v_init_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(v_map_2300_, v_f_2301_, v_init_2302_);
lean_dec_ref(v_map_2300_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(lean_object* v_00_u03c3_2304_, lean_object* v_00_u03b2_2305_, lean_object* v_map_2306_, lean_object* v_f_2307_, lean_object* v_init_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2307_, v_map_2306_, v_init_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___boxed(lean_object* v_00_u03c3_2310_, lean_object* v_00_u03b2_2311_, lean_object* v_map_2312_, lean_object* v_f_2313_, lean_object* v_init_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(v_00_u03c3_2310_, v_00_u03b2_2311_, v_map_2312_, v_f_2313_, v_init_2314_);
lean_dec_ref(v_map_2312_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(lean_object* v_simpThms_2316_, lean_object* v_as_2317_, lean_object* v_as_x27_2318_, lean_object* v_b_2319_, lean_object* v_a_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2316_, v_as_x27_2318_, v_b_2319_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___boxed(lean_object* v_simpThms_2329_, lean_object* v_as_2330_, lean_object* v_as_x27_2331_, lean_object* v_b_2332_, lean_object* v_a_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(v_simpThms_2329_, v_as_2330_, v_as_x27_2331_, v_b_2332_, v_a_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v_as_x27_2331_);
lean_dec(v_as_2330_);
lean_dec_ref(v_simpThms_2329_);
return v_res_2341_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, size_t v_x_2344_, lean_object* v_x_2345_){
_start:
{
uint8_t v___x_2346_; 
v___x_2346_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___redArg(v_x_2343_, v_x_2344_, v_x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
size_t v_x_29929__boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_x_29929__boxed_2351_ = lean_unbox_usize(v_x_2349_);
lean_dec(v_x_2349_);
v_res_2352_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_00_u03b2_2347_, v_x_2348_, v_x_29929__boxed_2351_, v_x_2350_);
lean_dec_ref(v_x_2350_);
lean_dec_ref(v_x_2348_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(lean_object* v_00_u03b2_2354_, lean_object* v_x_2355_, size_t v_x_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2355_, v_x_2356_, v_x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
size_t v_x_29940__boxed_2363_; lean_object* v_res_2364_; 
v_x_29940__boxed_2363_ = lean_unbox_usize(v_x_2361_);
lean_dec(v_x_2361_);
v_res_2364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(v_00_u03b2_2359_, v_x_2360_, v_x_29940__boxed_2363_, v_x_2362_);
lean_dec(v_x_2362_);
lean_dec_ref(v_x_2360_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(lean_object* v_00_u03b1_2365_, lean_object* v_00_u03c3_2366_, lean_object* v_f_2367_, lean_object* v_as_2368_, size_t v_i_2369_, size_t v_stop_2370_, lean_object* v_b_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_2367_, v_as_2368_, v_i_2369_, v_stop_2370_, v_b_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2373_, lean_object* v_00_u03c3_2374_, lean_object* v_f_2375_, lean_object* v_as_2376_, lean_object* v_i_2377_, lean_object* v_stop_2378_, lean_object* v_b_2379_){
_start:
{
size_t v_i_boxed_2380_; size_t v_stop_boxed_2381_; lean_object* v_res_2382_; 
v_i_boxed_2380_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_stop_boxed_2381_ = lean_unbox_usize(v_stop_2378_);
lean_dec(v_stop_2378_);
v_res_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(v_00_u03b1_2373_, v_00_u03c3_2374_, v_f_2375_, v_as_2376_, v_i_boxed_2380_, v_stop_boxed_2381_, v_b_2379_);
lean_dec_ref(v_as_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(lean_object* v_00_u03b1_2383_, lean_object* v_00_u03c3_2384_, lean_object* v_f_2385_, lean_object* v_as_2386_, size_t v_i_2387_, size_t v_stop_2388_, lean_object* v_b_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_2385_, v_as_2386_, v_i_2387_, v_stop_2388_, v_b_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2391_, lean_object* v_00_u03c3_2392_, lean_object* v_f_2393_, lean_object* v_as_2394_, lean_object* v_i_2395_, lean_object* v_stop_2396_, lean_object* v_b_2397_){
_start:
{
size_t v_i_boxed_2398_; size_t v_stop_boxed_2399_; lean_object* v_res_2400_; 
v_i_boxed_2398_ = lean_unbox_usize(v_i_2395_);
lean_dec(v_i_2395_);
v_stop_boxed_2399_ = lean_unbox_usize(v_stop_2396_);
lean_dec(v_stop_2396_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(v_00_u03b1_2391_, v_00_u03c3_2392_, v_f_2393_, v_as_2394_, v_i_boxed_2398_, v_stop_boxed_2399_, v_b_2397_);
lean_dec_ref(v_as_2394_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(lean_object* v_00_u03c3_2401_, lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_f_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2404_, v_x_2405_, v_x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___boxed(lean_object* v_00_u03c3_2408_, lean_object* v_00_u03b1_2409_, lean_object* v_00_u03b2_2410_, lean_object* v_f_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(v_00_u03c3_2408_, v_00_u03b1_2409_, v_00_u03b2_2410_, v_f_2411_, v_x_2412_, v_x_2413_);
lean_dec_ref(v_x_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(lean_object* v_00_u03b2_2415_, lean_object* v_m_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___boxed(lean_object* v_00_u03b2_2418_, lean_object* v_m_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(v_00_u03b2_2418_, v_m_2419_);
lean_dec_ref(v_m_2419_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_x_2422_, v_x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(v_00_u03b2_2425_, v_x_2426_, v_x_2427_);
lean_dec(v_x_2427_);
lean_dec_ref(v_x_2426_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_x_2430_, v_x_2431_, v_x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object* v_00_u03b2_2434_, lean_object* v_keys_2435_, lean_object* v_vals_2436_, lean_object* v_heq_2437_, lean_object* v_i_2438_, lean_object* v_k_2439_){
_start:
{
uint8_t v___x_2440_; 
v___x_2440_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___redArg(v_keys_2435_, v_i_2438_, v_k_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___boxed(lean_object* v_00_u03b2_2441_, lean_object* v_keys_2442_, lean_object* v_vals_2443_, lean_object* v_heq_2444_, lean_object* v_i_2445_, lean_object* v_k_2446_){
_start:
{
uint8_t v_res_2447_; lean_object* v_r_2448_; 
v_res_2447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_00_u03b2_2441_, v_keys_2442_, v_vals_2443_, v_heq_2444_, v_i_2445_, v_k_2446_);
lean_dec_ref(v_k_2446_);
lean_dec_ref(v_vals_2443_);
lean_dec_ref(v_keys_2442_);
v_r_2448_ = lean_box(v_res_2447_);
return v_r_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(lean_object* v_00_u03b2_2449_, lean_object* v_keys_2450_, lean_object* v_vals_2451_, lean_object* v_heq_2452_, lean_object* v_i_2453_, lean_object* v_k_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_keys_2450_, v_vals_2451_, v_i_2453_, v_k_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2456_, lean_object* v_keys_2457_, lean_object* v_vals_2458_, lean_object* v_heq_2459_, lean_object* v_i_2460_, lean_object* v_k_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(v_00_u03b2_2456_, v_keys_2457_, v_vals_2458_, v_heq_2459_, v_i_2460_, v_k_2461_);
lean_dec(v_k_2461_);
lean_dec_ref(v_vals_2458_);
lean_dec_ref(v_keys_2457_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(lean_object* v_00_u03b1_2463_, lean_object* v_00_u03b2_2464_, lean_object* v_00_u03c3_2465_, lean_object* v_f_2466_, lean_object* v_as_2467_, size_t v_i_2468_, size_t v_stop_2469_, lean_object* v_b_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_2466_, v_as_2467_, v_i_2468_, v_stop_2469_, v_b_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_00_u03b2_2473_, lean_object* v_00_u03c3_2474_, lean_object* v_f_2475_, lean_object* v_as_2476_, lean_object* v_i_2477_, lean_object* v_stop_2478_, lean_object* v_b_2479_){
_start:
{
size_t v_i_boxed_2480_; size_t v_stop_boxed_2481_; lean_object* v_res_2482_; 
v_i_boxed_2480_ = lean_unbox_usize(v_i_2477_);
lean_dec(v_i_2477_);
v_stop_boxed_2481_ = lean_unbox_usize(v_stop_2478_);
lean_dec(v_stop_2478_);
v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(v_00_u03b1_2472_, v_00_u03b2_2473_, v_00_u03c3_2474_, v_f_2475_, v_as_2476_, v_i_boxed_2480_, v_stop_boxed_2481_, v_b_2479_);
lean_dec_ref(v_as_2476_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object* v_00_u03c3_2483_, lean_object* v_00_u03b1_2484_, lean_object* v_00_u03b2_2485_, lean_object* v_f_2486_, lean_object* v_keys_2487_, lean_object* v_vals_2488_, lean_object* v_heq_2489_, lean_object* v_i_2490_, lean_object* v_acc_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_2486_, v_keys_2487_, v_vals_2488_, v_i_2490_, v_acc_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object* v_00_u03c3_2493_, lean_object* v_00_u03b1_2494_, lean_object* v_00_u03b2_2495_, lean_object* v_f_2496_, lean_object* v_keys_2497_, lean_object* v_vals_2498_, lean_object* v_heq_2499_, lean_object* v_i_2500_, lean_object* v_acc_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(v_00_u03c3_2493_, v_00_u03b1_2494_, v_00_u03b2_2495_, v_f_2496_, v_keys_2497_, v_vals_2498_, v_heq_2499_, v_i_2500_, v_acc_2501_);
lean_dec_ref(v_vals_2498_);
lean_dec_ref(v_keys_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(lean_object* v_00_u03c3_2503_, lean_object* v_00_u03b2_2504_, lean_object* v_map_2505_, lean_object* v_f_2506_, lean_object* v_init_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_map_2505_, v_f_2506_, v_init_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___boxed(lean_object* v_00_u03c3_2509_, lean_object* v_00_u03b2_2510_, lean_object* v_map_2511_, lean_object* v_f_2512_, lean_object* v_init_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(v_00_u03c3_2509_, v_00_u03b2_2510_, v_map_2511_, v_f_2512_, v_init_2513_);
lean_dec_ref(v_map_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12(lean_object* v_00_u03b2_2515_, lean_object* v_x_2516_, size_t v_x_2517_, lean_object* v_x_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___redArg(v_x_2516_, v_x_2517_, v_x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12___boxed(lean_object* v_00_u03b2_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
size_t v_x_29991__boxed_2524_; lean_object* v_res_2525_; 
v_x_29991__boxed_2524_ = lean_unbox_usize(v_x_2522_);
lean_dec(v_x_2522_);
v_res_2525_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12(v_00_u03b2_2520_, v_x_2521_, v_x_29991__boxed_2524_, v_x_2523_);
lean_dec(v_x_2523_);
lean_dec_ref(v_x_2521_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14(lean_object* v_00_u03b2_2526_, lean_object* v_x_2527_, size_t v_x_2528_, size_t v_x_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___redArg(v_x_2527_, v_x_2528_, v_x_2529_, v_x_2530_, v_x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14___boxed(lean_object* v_00_u03b2_2533_, lean_object* v_x_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
size_t v_x_30002__boxed_2539_; size_t v_x_30003__boxed_2540_; lean_object* v_res_2541_; 
v_x_30002__boxed_2539_ = lean_unbox_usize(v_x_2535_);
lean_dec(v_x_2535_);
v_x_30003__boxed_2540_ = lean_unbox_usize(v_x_2536_);
lean_dec(v_x_2536_);
v_res_2541_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14(v_00_u03b2_2533_, v_x_2534_, v_x_30002__boxed_2539_, v_x_30003__boxed_2540_, v_x_2537_, v_x_2538_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg(lean_object* v_map_2542_, lean_object* v_f_2543_, lean_object* v_init_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2543_, v_map_2542_, v_init_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg___boxed(lean_object* v_map_2546_, lean_object* v_f_2547_, lean_object* v_init_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___redArg(v_map_2546_, v_f_2547_, v_init_2548_);
lean_dec_ref(v_map_2546_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30(lean_object* v_00_u03c3_2550_, lean_object* v_00_u03b2_2551_, lean_object* v_map_2552_, lean_object* v_f_2553_, lean_object* v_init_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2553_, v_map_2552_, v_init_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30___boxed(lean_object* v_00_u03c3_2556_, lean_object* v_00_u03b2_2557_, lean_object* v_map_2558_, lean_object* v_f_2559_, lean_object* v_init_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__30(v_00_u03c3_2556_, v_00_u03b2_2557_, v_map_2558_, v_f_2559_, v_init_2560_);
lean_dec_ref(v_map_2558_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21(lean_object* v_00_u03b2_2562_, lean_object* v_keys_2563_, lean_object* v_vals_2564_, lean_object* v_heq_2565_, lean_object* v_i_2566_, lean_object* v_k_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___redArg(v_keys_2563_, v_vals_2564_, v_i_2566_, v_k_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21___boxed(lean_object* v_00_u03b2_2569_, lean_object* v_keys_2570_, lean_object* v_vals_2571_, lean_object* v_heq_2572_, lean_object* v_i_2573_, lean_object* v_k_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__12_spec__21(v_00_u03b2_2569_, v_keys_2570_, v_vals_2571_, v_heq_2572_, v_i_2573_, v_k_2574_);
lean_dec(v_k_2574_);
lean_dec_ref(v_vals_2571_);
lean_dec_ref(v_keys_2570_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24(lean_object* v_00_u03b2_2576_, lean_object* v_n_2577_, lean_object* v_k_2578_, lean_object* v_v_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24___redArg(v_n_2577_, v_k_2578_, v_v_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25(lean_object* v_00_u03b2_2581_, size_t v_depth_2582_, lean_object* v_keys_2583_, lean_object* v_vals_2584_, lean_object* v_heq_2585_, lean_object* v_i_2586_, lean_object* v_entries_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___redArg(v_depth_2582_, v_keys_2583_, v_vals_2584_, v_i_2586_, v_entries_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25___boxed(lean_object* v_00_u03b2_2589_, lean_object* v_depth_2590_, lean_object* v_keys_2591_, lean_object* v_vals_2592_, lean_object* v_heq_2593_, lean_object* v_i_2594_, lean_object* v_entries_2595_){
_start:
{
size_t v_depth_boxed_2596_; lean_object* v_res_2597_; 
v_depth_boxed_2596_ = lean_unbox_usize(v_depth_2590_);
lean_dec(v_depth_2590_);
v_res_2597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__25(v_00_u03b2_2589_, v_depth_boxed_2596_, v_keys_2591_, v_vals_2592_, v_heq_2593_, v_i_2594_, v_entries_2595_);
lean_dec_ref(v_vals_2592_);
lean_dec_ref(v_keys_2591_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30(lean_object* v_x_2598_, lean_object* v_keys_2599_, lean_object* v_v_2600_, lean_object* v_k_2601_, lean_object* v_as_2602_, lean_object* v_k_2603_, lean_object* v_x_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_, lean_object* v_x_2607_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___redArg(v_x_2598_, v_keys_2599_, v_v_2600_, v_k_2601_, v_as_2602_, v_k_2603_, v_x_2604_, v_x_2605_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30___boxed(lean_object* v_x_2609_, lean_object* v_keys_2610_, lean_object* v_v_2611_, lean_object* v_k_2612_, lean_object* v_as_2613_, lean_object* v_k_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__3_spec__17_spec__30(v_x_2609_, v_keys_2610_, v_v_2611_, v_k_2612_, v_as_2613_, v_k_2614_, v_x_2615_, v_x_2616_, v_x_2617_, v_x_2618_);
lean_dec_ref(v_k_2614_);
lean_dec_ref(v_keys_2610_);
lean_dec(v_x_2609_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2_spec__14_spec__24_spec__31___redArg(v_x_2621_, v_x_2622_, v_x_2623_, v_x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(lean_object* v_xs_2626_, lean_object* v_j_2627_){
_start:
{
lean_object* v_zero_2628_; uint8_t v_isZero_2629_; 
v_zero_2628_ = lean_unsigned_to_nat(0u);
v_isZero_2629_ = lean_nat_dec_eq(v_j_2627_, v_zero_2628_);
if (v_isZero_2629_ == 1)
{
lean_dec(v_j_2627_);
return v_xs_2626_;
}
else
{
lean_object* v_one_2630_; lean_object* v_n_2631_; lean_object* v___x_2632_; lean_object* v_priority_2633_; lean_object* v___x_2634_; lean_object* v_priority_2635_; uint8_t v___x_2636_; 
v_one_2630_ = lean_unsigned_to_nat(1u);
v_n_2631_ = lean_nat_sub(v_j_2627_, v_one_2630_);
v___x_2632_ = lean_array_fget_borrowed(v_xs_2626_, v_n_2631_);
v_priority_2633_ = lean_ctor_get(v___x_2632_, 3);
v___x_2634_ = lean_array_fget_borrowed(v_xs_2626_, v_j_2627_);
v_priority_2635_ = lean_ctor_get(v___x_2634_, 3);
v___x_2636_ = lean_nat_dec_lt(v_priority_2633_, v_priority_2635_);
if (v___x_2636_ == 0)
{
lean_dec(v_n_2631_);
lean_dec(v_j_2627_);
return v_xs_2626_;
}
else
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_array_fswap(v_xs_2626_, v_j_2627_, v_n_2631_);
lean_dec(v_j_2627_);
v_xs_2626_ = v___x_2637_;
v_j_2627_ = v_n_2631_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(lean_object* v_xs_2639_, lean_object* v_i_2640_, lean_object* v_fuel_2641_){
_start:
{
lean_object* v_zero_2642_; uint8_t v_isZero_2643_; 
v_zero_2642_ = lean_unsigned_to_nat(0u);
v_isZero_2643_ = lean_nat_dec_eq(v_fuel_2641_, v_zero_2642_);
if (v_isZero_2643_ == 1)
{
lean_dec(v_fuel_2641_);
lean_dec(v_i_2640_);
return v_xs_2639_;
}
else
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = lean_array_get_size(v_xs_2639_);
v___x_2645_ = lean_nat_dec_lt(v_i_2640_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec(v_fuel_2641_);
lean_dec(v_i_2640_);
return v_xs_2639_;
}
else
{
lean_object* v_one_2646_; lean_object* v_n_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_one_2646_ = lean_unsigned_to_nat(1u);
v_n_2647_ = lean_nat_sub(v_fuel_2641_, v_one_2646_);
lean_dec(v_fuel_2641_);
lean_inc(v_i_2640_);
v___x_2648_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_xs_2639_, v_i_2640_);
v___x_2649_ = lean_nat_add(v_i_2640_, v_one_2646_);
lean_dec(v_i_2640_);
v_xs_2639_ = v___x_2648_;
v_i_2640_ = v___x_2649_;
v_fuel_2641_ = v_n_2647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(lean_object* v_a_2654_, lean_object* v_as_2655_, size_t v_sz_2656_, size_t v_i_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_usize_dec_lt(v_i_2657_, v_sz_2656_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec_ref(v_a_2654_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_b_2658_);
return v___x_2667_;
}
else
{
lean_object* v_a_2668_; lean_object* v_pattern_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v_b_2658_);
v_a_2668_ = lean_array_uget_borrowed(v_as_2655_, v_i_2657_);
v_pattern_2669_ = lean_ctor_get(v_a_2668_, 0);
lean_inc_ref(v_a_2654_);
lean_inc_ref(v_pattern_2669_);
v___x_2670_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_2669_, v_a_2654_, v___x_2666_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2693_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2693_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2693_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_box(0);
if (lean_obj_tag(v_a_2671_) == 1)
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v_a_2654_);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_a_2671_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v_a_2671_, 0);
lean_dec(v_unused_2688_);
v___x_2677_ = v_a_2671_;
v_isShared_2678_ = v_isSharedCheck_2687_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v_a_2671_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2687_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2681_; 
lean_inc(v_a_2668_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_a_2668_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2679_);
v___x_2681_ = v___x_2677_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v___x_2675_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2682_);
v___x_2684_ = v___x_2673_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; 
lean_del_object(v___x_2673_);
lean_dec(v_a_2671_);
v___x_2689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0));
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_add(v_i_2657_, v___x_2690_);
v_i_2657_ = v___x_2691_;
v_b_2658_ = v___x_2689_;
goto _start;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_a_2654_);
v_a_2694_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2670_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2670_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___boxed(lean_object* v_a_2702_, lean_object* v_as_2703_, lean_object* v_sz_2704_, lean_object* v_i_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
size_t v_sz_boxed_2714_; size_t v_i_boxed_2715_; lean_object* v_res_2716_; 
v_sz_boxed_2714_ = lean_unbox_usize(v_sz_2704_);
lean_dec(v_sz_2704_);
v_i_boxed_2715_ = lean_unbox_usize(v_i_2705_);
lean_dec(v_i_2705_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v_a_2702_, v_as_2703_, v_sz_boxed_2714_, v_i_boxed_2715_, v_b_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec_ref(v_as_2703_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object* v_database_2717_, lean_object* v_e_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2788_; 
v___x_2726_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_2718_, v_a_2722_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2788_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2788_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2727_, v_a_2720_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2779_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2779_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2779_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_specs_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v_specs_2736_ = lean_ctor_get(v_database_2717_, 0);
v___x_2737_ = l_Lean_Meta_Sym_getMatch___redArg(v_specs_2736_, v_a_2732_);
v___x_2738_ = lean_array_get_size(v___x_2737_);
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_dec_eq(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; size_t v_sz_2744_; size_t v___x_2745_; lean_object* v___x_2746_; 
lean_del_object(v___x_2734_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(v___x_2737_, v___x_2741_, v___x_2738_);
v___x_2743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1___closed__0));
v_sz_2744_ = lean_array_size(v___x_2742_);
v___x_2745_ = ((size_t)0ULL);
v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v_a_2732_, v___x_2742_, v_sz_2744_, v___x_2745_, v___x_2743_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2762_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2762_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2762_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_fst_2751_; 
v_fst_2751_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_fst_2751_);
lean_dec(v_a_2747_);
if (lean_obj_tag(v_fst_2751_) == 0)
{
lean_object* v___x_2753_; 
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2742_);
v___x_2753_ = v___x_2729_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2742_);
v___x_2753_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2753_);
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
lean_object* v_val_2758_; lean_object* v___x_2760_; 
lean_dec_ref(v___x_2742_);
lean_del_object(v___x_2729_);
v_val_2758_ = lean_ctor_get(v_fst_2751_, 0);
lean_inc(v_val_2758_);
lean_dec_ref_known(v_fst_2751_, 1);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_val_2758_);
v___x_2760_ = v___x_2749_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_val_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v___x_2742_);
lean_del_object(v___x_2729_);
v_a_2763_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2746_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2746_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v_a_2732_);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_array_fget(v___x_2737_, v___x_2771_);
lean_dec_ref(v___x_2737_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 1);
lean_ctor_set(v___x_2729_, 0, v___x_2772_);
v___x_2774_ = v___x_2729_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2774_);
v___x_2776_ = v___x_2734_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_del_object(v___x_2729_);
v_a_2780_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2731_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2731_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(lean_object* v_database_2789_, lean_object* v_e_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(v_database_2789_, v_e_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec_ref(v_database_2789_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(lean_object* v_xs_2799_, lean_object* v_j_2800_, lean_object* v_h_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_xs_2799_, v_j_2800_);
return v___x_2802_;
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
