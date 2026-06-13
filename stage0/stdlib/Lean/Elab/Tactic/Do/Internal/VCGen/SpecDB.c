// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
// Imports: public import Lean.Elab.Tactic.Do.Attr public import Lean.Meta.Sym.Pattern public import Lean.Meta.DiscrTree.Util import Lean.Meta.Sym.Simp.DiscrTree import Lean.Meta.Sym.Util
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default;
extern lean_object* l_Lean_Meta_Sym_instInhabitedPattern_default;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = " was not a Triple. Should not happen with the previous tests in place."};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PostShape"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "args"};
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20_spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20_spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32_spec__37___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "could not migrate spec theorem "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__4, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(lean_object* v_a_592_, uint8_t v___x_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v_a_597_, lean_object* v_proof_598_, lean_object* v_prio_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v_config_608_; uint8_t v_trackZetaDelta_609_; lean_object* v_zetaDeltaSet_610_; lean_object* v_lctx_611_; lean_object* v_localInstances_612_; lean_object* v_defEqCtx_x3f_613_; lean_object* v_synthPendingDepth_614_; lean_object* v_canUnfold_x3f_615_; uint8_t v_univApprox_616_; uint8_t v_inTypeClassResolution_617_; uint8_t v_cacheInferType_618_; uint64_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_607_ = l_Lean_Meta_simpGlobalConfig;
v_config_608_ = lean_ctor_get(v___x_607_, 0);
v_trackZetaDelta_609_ = lean_ctor_get_uint8(v___y_602_, sizeof(void*)*7);
v_zetaDeltaSet_610_ = lean_ctor_get(v___y_602_, 1);
v_lctx_611_ = lean_ctor_get(v___y_602_, 2);
v_localInstances_612_ = lean_ctor_get(v___y_602_, 3);
v_defEqCtx_x3f_613_ = lean_ctor_get(v___y_602_, 4);
v_synthPendingDepth_614_ = lean_ctor_get(v___y_602_, 5);
v_canUnfold_x3f_615_ = lean_ctor_get(v___y_602_, 6);
v_univApprox_616_ = lean_ctor_get_uint8(v___y_602_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_617_ = lean_ctor_get_uint8(v___y_602_, sizeof(void*)*7 + 2);
v_cacheInferType_618_ = lean_ctor_get_uint8(v___y_602_, sizeof(void*)*7 + 3);
v___x_619_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_608_);
lean_inc_ref(v_config_608_);
v___x_620_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_620_, 0, v_config_608_);
lean_ctor_set_uint64(v___x_620_, sizeof(void*)*1, v___x_619_);
lean_inc(v_canUnfold_x3f_615_);
lean_inc(v_synthPendingDepth_614_);
lean_inc(v_defEqCtx_x3f_613_);
lean_inc_ref(v_localInstances_612_);
lean_inc_ref(v_lctx_611_);
lean_inc(v_zetaDeltaSet_610_);
v___x_621_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v_zetaDeltaSet_610_);
lean_ctor_set(v___x_621_, 2, v_lctx_611_);
lean_ctor_set(v___x_621_, 3, v_localInstances_612_);
lean_ctor_set(v___x_621_, 4, v_defEqCtx_x3f_613_);
lean_ctor_set(v___x_621_, 5, v_synthPendingDepth_614_);
lean_ctor_set(v___x_621_, 6, v_canUnfold_x3f_615_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*7, v_trackZetaDelta_609_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*7 + 1, v_univApprox_616_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*7 + 2, v_inTypeClassResolution_617_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*7 + 3, v_cacheInferType_618_);
v___x_622_ = l_Lean_Meta_forallMetaTelescope(v_a_592_, v___x_593_, v___x_621_, v___y_603_, v___y_604_, v___y_605_);
lean_dec_ref_known(v___x_621_, 7);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_snd_624_; lean_object* v_fst_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_709_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v_snd_624_ = lean_ctor_get(v_a_623_, 1);
v_fst_625_ = lean_ctor_get(v_a_623_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_709_ == 0)
{
v___x_627_ = v_a_623_;
v_isShared_628_ = v_isSharedCheck_709_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_624_);
lean_inc(v_fst_625_);
lean_dec(v_a_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_709_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_707_; 
v_snd_629_ = lean_ctor_get(v_snd_624_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_snd_624_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_snd_624_, 0);
lean_dec(v_unused_708_);
v___x_631_ = v_snd_624_;
v_isShared_632_ = v_isSharedCheck_707_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_dec(v_snd_624_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_707_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Meta_whnfR(v_snd_629_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_n(v_a_634_, 2);
lean_dec_ref_known(v___x_633_, 1);
v___x_648_ = l_Lean_Expr_cleanupAnnotations(v_a_634_);
v___x_649_ = l_Lean_Expr_isApp(v___x_648_);
if (v___x_649_ == 0)
{
lean_dec_ref(v___x_648_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_648_);
v___x_651_ = l_Lean_Expr_isApp(v___x_650_);
if (v___x_651_ == 0)
{
lean_dec_ref(v___x_650_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v_arg_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_arg_652_ = lean_ctor_get(v___x_650_, 1);
lean_inc_ref(v_arg_652_);
v___x_653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_650_);
v___x_654_ = l_Lean_Expr_isApp(v___x_653_);
if (v___x_654_ == 0)
{
lean_dec_ref(v___x_653_);
lean_dec_ref(v_arg_652_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_653_);
v___x_656_ = l_Lean_Expr_isApp(v___x_655_);
if (v___x_656_ == 0)
{
lean_dec_ref(v___x_655_);
lean_dec_ref(v_arg_652_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_655_);
v___x_658_ = l_Lean_Expr_isApp(v___x_657_);
if (v___x_658_ == 0)
{
lean_dec_ref(v___x_657_);
lean_dec_ref(v_arg_652_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_657_);
v___x_660_ = l_Lean_Expr_isApp(v___x_659_);
if (v___x_660_ == 0)
{
lean_dec_ref(v___x_659_);
lean_dec_ref(v_arg_652_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v_arg_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_arg_661_ = lean_ctor_get(v___x_659_, 1);
lean_inc_ref(v_arg_661_);
v___x_662_ = l_Lean_Expr_appFnCleanup___redArg(v___x_659_);
v___x_663_ = l_Lean_Expr_isApp(v___x_662_);
if (v___x_663_ == 0)
{
lean_dec_ref(v___x_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v_arg_652_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = l_Lean_Expr_appFnCleanup___redArg(v___x_662_);
v___x_665_ = l_Lean_Expr_isConstOf(v___x_664_, v___x_594_);
if (v___x_665_ == 0)
{
lean_dec_ref(v___x_664_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v_arg_652_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v___y_636_ = v___y_600_;
v___y_637_ = v___y_601_;
v___y_638_ = v___y_602_;
v___y_639_ = v___y_603_;
v___y_640_ = v___y_604_;
v___y_641_ = v___y_605_;
goto v___jp_635_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_dec(v_a_634_);
lean_del_object(v___x_631_);
v___x_666_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2));
v___x_667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3));
v___x_668_ = l_Lean_Name_mkStr4(v___x_595_, v___x_596_, v___x_666_, v___x_667_);
v___x_669_ = lean_box(0);
v___x_670_ = l_Lean_Expr_constLevels_x21(v___x_664_);
lean_dec_ref(v___x_664_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = l_List_get_x21Internal___redArg(v___x_669_, v___x_670_, v___x_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 1);
lean_ctor_set(v___x_627_, 1, v___x_673_);
lean_ctor_set(v___x_627_, 0, v___x_672_);
v___x_675_ = v___x_627_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_698_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = l_Lean_mkConst(v___x_668_, v___x_675_);
v___x_677_ = l_Lean_Expr_app___override(v___x_676_, v_arg_661_);
v___x_678_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(v_fst_625_, v___x_677_, v_arg_652_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_a_679_);
v___x_684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_684_, 0, v_a_597_);
lean_ctor_set(v___x_684_, 1, v_proof_598_);
lean_ctor_set(v___x_684_, 2, v___x_683_);
lean_ctor_set(v___x_684_, 3, v_prio_599_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_685_);
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
v_a_690_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_678_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_678_);
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
}
}
}
}
}
}
}
}
v___jp_635_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = l_Lean_MessageData_ofExpr(v_a_634_);
v___x_643_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1);
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 7);
lean_ctor_set(v___x_631_, 1, v___x_643_);
lean_ctor_set(v___x_631_, 0, v___x_642_);
v___x_645_ = v___x_631_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_645_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_646_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_del_object(v___x_631_);
lean_del_object(v___x_627_);
lean_dec(v_fst_625_);
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v_a_699_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_633_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_633_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_prio_599_);
lean_dec_ref(v_proof_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v___x_596_);
lean_dec_ref(v___x_595_);
v_a_710_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_622_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_622_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed(lean_object* v_a_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_a_723_, lean_object* v_proof_724_, lean_object* v_prio_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v___x_16832__boxed_733_; lean_object* v_res_734_; 
v___x_16832__boxed_733_ = lean_unbox(v___x_719_);
v_res_734_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(v_a_718_, v___x_16832__boxed_733_, v___x_720_, v___x_721_, v___x_722_, v_a_723_, v_proof_724_, v_prio_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___x_720_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(lean_object* v_proof_735_, lean_object* v_prio_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
lean_inc_ref(v_proof_735_);
v___x_744_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(v_proof_735_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_fst_746_; lean_object* v_snd_747_; lean_object* v___x_748_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_fst_746_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_fst_746_);
v_snd_747_ = lean_ctor_get(v_a_745_, 1);
lean_inc_n(v_snd_747_, 2);
lean_dec(v_a_745_);
lean_inc(v_a_742_);
lean_inc_ref(v_a_741_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
v___x_748_ = lean_infer_type(v_snd_747_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_780_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_a_749_, v_a_740_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_780_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_780_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_780_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_755_ = l_Lean_Expr_getForallBody(v_a_751_);
v___x_756_ = l_Lean_Expr_getAppFn(v___x_755_);
lean_dec_ref(v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2));
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3));
v___x_759_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5));
v___x_760_ = l_Lean_Expr_isConstOf(v___x_756_, v___x_759_);
lean_dec_ref(v___x_756_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec(v_a_751_);
lean_dec(v_snd_747_);
lean_dec(v_fst_746_);
lean_dec(v_prio_736_);
lean_dec_ref(v_proof_735_);
v___x_761_ = lean_box(0);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_761_);
v___x_763_ = v___x_753_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
lean_object* v___x_765_; 
lean_del_object(v___x_753_);
v___x_765_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(v_snd_747_, v_fst_746_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; uint8_t v___x_770_; lean_object* v___x_771_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = 0;
v___x_768_ = lean_box(v___x_767_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed), 15, 8);
lean_closure_set(v___f_769_, 0, v_a_751_);
lean_closure_set(v___f_769_, 1, v___x_768_);
lean_closure_set(v___f_769_, 2, v___x_759_);
lean_closure_set(v___f_769_, 3, v___x_757_);
lean_closure_set(v___f_769_, 4, v___x_758_);
lean_closure_set(v___f_769_, 5, v_a_766_);
lean_closure_set(v___f_769_, 6, v_proof_735_);
lean_closure_set(v___f_769_, 7, v_prio_736_);
v___x_770_ = 0;
v___x_771_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v___f_769_, v___x_770_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_771_;
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_a_751_);
lean_dec(v_prio_736_);
lean_dec_ref(v_proof_735_);
v_a_772_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_765_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_765_);
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
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_snd_747_);
lean_dec(v_fst_746_);
lean_dec(v_prio_736_);
lean_dec_ref(v_proof_735_);
v_a_781_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_748_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_748_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_prio_736_);
lean_dec_ref(v_proof_735_);
v_a_789_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_744_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_744_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___boxed(lean_object* v_proof_797_, lean_object* v_prio_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(v_proof_797_, v_prio_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(lean_object* v_00_u03b1_807_, lean_object* v_msg_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v_msg_808_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___boxed(lean_object* v_00_u03b1_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(v_00_u03b1_817_, v_msg_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(lean_object* v_ty_827_, lean_object* v_acc_828_){
_start:
{
if (lean_obj_tag(v_ty_827_) == 7)
{
lean_object* v_binderType_829_; lean_object* v_body_830_; lean_object* v___x_831_; 
v_binderType_829_ = lean_ctor_get(v_ty_827_, 1);
lean_inc_ref(v_binderType_829_);
v_body_830_ = lean_ctor_get(v_ty_827_, 2);
lean_inc_ref(v_body_830_);
lean_dec_ref_known(v_ty_827_, 3);
v___x_831_ = lean_array_push(v_acc_828_, v_binderType_829_);
v_ty_827_ = v_body_830_;
v_acc_828_ = v___x_831_;
goto _start;
}
else
{
lean_dec_ref(v_ty_827_);
return v_acc_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(lean_object* v_k_833_, lean_object* v_i_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_sub(v_k_833_, v___x_835_);
v___x_837_ = lean_nat_sub(v___x_836_, v_i_834_);
lean_dec(v___x_836_);
v___x_838_ = l_Lean_mkBVar(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed(lean_object* v_k_839_, lean_object* v_i_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(v_k_839_, v_i_840_);
lean_dec(v_i_840_);
lean_dec(v_k_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(lean_object* v_pattern_842_, lean_object* v_eqTy_843_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Expr_isForall(v_eqTy_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref(v_eqTy_843_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_pattern_842_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v_levelParams_847_; lean_object* v_varTypes_848_; lean_object* v_pattern_849_; lean_object* v_fnInfos_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_868_; 
v_levelParams_847_ = lean_ctor_get(v_pattern_842_, 0);
v_varTypes_848_ = lean_ctor_get(v_pattern_842_, 1);
v_pattern_849_ = lean_ctor_get(v_pattern_842_, 3);
v_fnInfos_850_ = lean_ctor_get(v_pattern_842_, 4);
v_isSharedCheck_868_ = !lean_is_exclusive(v_pattern_842_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; 
v_unused_869_ = lean_ctor_get(v_pattern_842_, 5);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_pattern_842_, 2);
lean_dec(v_unused_870_);
v___x_852_ = v_pattern_842_;
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_fnInfos_850_);
lean_inc(v_pattern_849_);
lean_inc(v_varTypes_848_);
lean_inc(v_levelParams_847_);
lean_dec(v_pattern_842_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_868_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_extraDomains_856_; lean_object* v_k_857_; lean_object* v___f_858_; lean_object* v_liftedPattern_859_; lean_object* v_newBVars_860_; lean_object* v_newPatternExpr_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_newPattern_865_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1));
v_extraDomains_856_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(v_eqTy_843_, v___x_855_);
v_k_857_ = lean_array_get_size(v_extraDomains_856_);
v___f_858_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed), 2, 1);
lean_closure_set(v___f_858_, 0, v_k_857_);
v_liftedPattern_859_ = lean_expr_lift_loose_bvars(v_pattern_849_, v___x_854_, v_k_857_);
lean_dec_ref(v_pattern_849_);
v_newBVars_860_ = l_Array_ofFn___redArg(v_k_857_, v___f_858_);
v_newPatternExpr_861_ = l_Lean_mkAppN(v_liftedPattern_859_, v_newBVars_860_);
lean_dec_ref(v_newBVars_860_);
v___x_862_ = l_Array_append___redArg(v_varTypes_848_, v_extraDomains_856_);
lean_dec_ref(v_extraDomains_856_);
v___x_863_ = lean_box(0);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 5, v___x_863_);
lean_ctor_set(v___x_852_, 3, v_newPatternExpr_861_);
lean_ctor_set(v___x_852_, 2, v___x_863_);
lean_ctor_set(v___x_852_, 1, v___x_862_);
v_newPattern_865_ = v___x_852_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_levelParams_847_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_newPatternExpr_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_fnInfos_850_);
lean_ctor_set(v_reuseFailAlloc_867_, 5, v___x_863_);
v_newPattern_865_ = v_reuseFailAlloc_867_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_newPattern_865_);
lean_ctor_set(v___x_866_, 1, v_k_857_);
return v___x_866_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(lean_object* v_body_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_885_; uint8_t v___x_886_; 
lean_inc_ref(v_body_874_);
v___x_885_ = l_Lean_Expr_cleanupAnnotations(v_body_874_);
v___x_886_ = l_Lean_Expr_isApp(v___x_885_);
if (v___x_886_ == 0)
{
lean_dec_ref(v___x_885_);
goto v___jp_880_;
}
else
{
lean_object* v_arg_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_arg_887_ = lean_ctor_get(v___x_885_, 1);
lean_inc_ref(v_arg_887_);
v___x_888_ = l_Lean_Expr_appFnCleanup___redArg(v___x_885_);
v___x_889_ = l_Lean_Expr_isApp(v___x_888_);
if (v___x_889_ == 0)
{
lean_dec_ref(v___x_888_);
lean_dec_ref(v_arg_887_);
goto v___jp_880_;
}
else
{
lean_object* v_arg_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_arg_890_ = lean_ctor_get(v___x_888_, 1);
lean_inc_ref(v_arg_890_);
v___x_891_ = l_Lean_Expr_appFnCleanup___redArg(v___x_888_);
v___x_892_ = l_Lean_Expr_isApp(v___x_891_);
if (v___x_892_ == 0)
{
lean_dec_ref(v___x_891_);
lean_dec_ref(v_arg_890_);
lean_dec_ref(v_arg_887_);
goto v___jp_880_;
}
else
{
lean_object* v_arg_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_arg_893_ = lean_ctor_get(v___x_891_, 1);
lean_inc_ref(v_arg_893_);
v___x_894_ = l_Lean_Expr_appFnCleanup___redArg(v___x_891_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1));
v___x_896_ = l_Lean_Expr_isConstOf(v___x_894_, v___x_895_);
lean_dec_ref(v___x_894_);
if (v___x_896_ == 0)
{
lean_dec_ref(v_arg_893_);
lean_dec_ref(v_arg_890_);
lean_dec_ref(v_arg_887_);
goto v___jp_880_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v_body_874_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_arg_893_);
lean_ctor_set(v___x_897_, 1, v_arg_887_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_arg_890_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
}
v___jp_880_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1);
v___x_882_ = l_Lean_indentExpr(v_body_874_);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v___x_883_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___boxed(lean_object* v_body_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(v_body_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(lean_object* v_declName_908_, lean_object* v_prio_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; 
lean_inc(v_declName_908_);
v___x_915_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern(v_declName_908_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v_fst_917_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_fst_917_);
v_snd_918_ = lean_ctor_get(v_a_916_, 1);
lean_inc_n(v_snd_918_, 2);
lean_dec(v_a_916_);
v___f_919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0));
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1));
v___x_922_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(lean_box(0), v_fst_917_, v_snd_918_, v___f_919_, v_snd_918_, v___x_921_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_950_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_950_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_950_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_950_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_snd_927_; lean_object* v_fst_928_; lean_object* v_fst_929_; lean_object* v_snd_930_; lean_object* v___x_931_; lean_object* v_fst_932_; lean_object* v_snd_933_; uint8_t v___y_935_; uint8_t v___x_947_; 
v_snd_927_ = lean_ctor_get(v_a_923_, 1);
lean_inc(v_snd_927_);
v_fst_928_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_fst_928_);
lean_dec(v_a_923_);
v_fst_929_ = lean_ctor_get(v_snd_927_, 0);
lean_inc(v_fst_929_);
v_snd_930_ = lean_ctor_get(v_snd_927_, 1);
lean_inc(v_snd_930_);
lean_dec(v_snd_927_);
v___x_931_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(v_fst_928_, v_fst_929_);
v_fst_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_fst_932_);
v_snd_933_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_snd_933_);
lean_dec_ref(v___x_931_);
v___x_947_ = lean_nat_dec_eq(v_snd_933_, v___x_920_);
if (v___x_947_ == 0)
{
lean_dec(v_snd_930_);
v___y_935_ = v___x_947_;
goto v___jp_934_;
}
else
{
lean_object* v_pattern_948_; uint8_t v___x_949_; 
v_pattern_948_ = lean_ctor_get(v_fst_932_, 3);
v___x_949_ = lean_expr_eqv(v_pattern_948_, v_snd_930_);
lean_dec(v_snd_930_);
v___y_935_ = v___x_949_;
goto v___jp_934_;
}
v___jp_934_:
{
if (v___y_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_declName_908_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_snd_933_);
v___x_938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_938_, 0, v_fst_932_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
lean_ctor_set(v___x_938_, 3, v_prio_909_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_939_);
v___x_941_ = v___x_925_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_945_; 
lean_dec(v_snd_933_);
lean_dec(v_fst_932_);
lean_dec(v_prio_909_);
lean_dec(v_declName_908_);
v___x_943_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_943_);
v___x_945_ = v___x_925_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec(v_prio_909_);
lean_dec(v_declName_908_);
v_a_951_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_922_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_922_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec(v_prio_909_);
lean_dec(v_declName_908_);
v_a_959_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_915_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_915_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___boxed(lean_object* v_declName_967_, lean_object* v_prio_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_declName_967_, v_prio_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__0(lean_object* v_x1_975_, lean_object* v_x2_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_array_push(v_x1_975_, v_x2_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(lean_object* v_f_978_, lean_object* v_as_979_, size_t v_i_980_, size_t v_stop_981_, lean_object* v_b_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_eq(v_i_980_, v_stop_981_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; size_t v___x_986_; size_t v___x_987_; 
v___x_984_ = lean_array_uget_borrowed(v_as_979_, v_i_980_);
lean_inc(v_f_978_);
lean_inc(v___x_984_);
v___x_985_ = lean_apply_2(v_f_978_, v_b_982_, v___x_984_);
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_980_, v___x_986_);
v_i_980_ = v___x_987_;
v_b_982_ = v___x_985_;
goto _start;
}
else
{
lean_dec(v_f_978_);
return v_b_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg___boxed(lean_object* v_f_989_, lean_object* v_as_990_, lean_object* v_i_991_, lean_object* v_stop_992_, lean_object* v_b_993_){
_start:
{
size_t v_i_boxed_994_; size_t v_stop_boxed_995_; lean_object* v_res_996_; 
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_stop_boxed_995_ = lean_unbox_usize(v_stop_992_);
lean_dec(v_stop_992_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_989_, v_as_990_, v_i_boxed_994_, v_stop_boxed_995_, v_b_993_);
lean_dec_ref(v_as_990_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(lean_object* v_f_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
lean_object* v_vs_1000_; lean_object* v_children_1001_; lean_object* v___x_1002_; lean_object* v_s_1004_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_vs_1000_ = lean_ctor_get(v_x_999_, 0);
v_children_1001_ = lean_ctor_get(v_x_999_, 1);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_array_get_size(v_vs_1000_);
v___x_1015_ = lean_nat_dec_lt(v___x_1002_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_children_1001_);
v___x_1017_ = lean_nat_dec_lt(v___x_1002_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_f_997_);
return v_x_998_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_le(v___x_1016_, v___x_1016_);
if (v___x_1018_ == 0)
{
if (v___x_1017_ == 0)
{
lean_dec(v_f_997_);
return v_x_998_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1016_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_997_, v_children_1001_, v___x_1019_, v___x_1020_, v_x_998_);
return v___x_1021_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1016_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_997_, v_children_1001_, v___x_1022_, v___x_1023_, v_x_998_);
return v___x_1024_;
}
}
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_le(v___x_1014_, v___x_1014_);
if (v___x_1025_ == 0)
{
if (v___x_1015_ == 0)
{
v_s_1004_ = v_x_998_;
goto v___jp_1003_;
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1014_);
lean_inc(v_f_997_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_997_, v_vs_1000_, v___x_1026_, v___x_1027_, v_x_998_);
v_s_1004_ = v___x_1028_;
goto v___jp_1003_;
}
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = lean_usize_of_nat(v___x_1014_);
lean_inc(v_f_997_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_997_, v_vs_1000_, v___x_1029_, v___x_1030_, v_x_998_);
v_s_1004_ = v___x_1031_;
goto v___jp_1003_;
}
}
v___jp_1003_:
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_array_get_size(v_children_1001_);
v___x_1006_ = lean_nat_dec_lt(v___x_1002_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_dec(v_f_997_);
return v_s_1004_;
}
else
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_nat_dec_le(v___x_1005_, v___x_1005_);
if (v___x_1007_ == 0)
{
if (v___x_1006_ == 0)
{
lean_dec(v_f_997_);
return v_s_1004_;
}
else
{
size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = lean_usize_of_nat(v___x_1005_);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_997_, v_children_1001_, v___x_1008_, v___x_1009_, v_s_1004_);
return v___x_1010_;
}
}
else
{
size_t v___x_1011_; size_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = ((size_t)0ULL);
v___x_1012_ = lean_usize_of_nat(v___x_1005_);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_997_, v_children_1001_, v___x_1011_, v___x_1012_, v_s_1004_);
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(lean_object* v_f_1032_, lean_object* v_as_1033_, size_t v_i_1034_, size_t v_stop_1035_, lean_object* v_b_1036_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_eq(v_i_1034_, v_stop_1035_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v_snd_1039_; lean_object* v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; 
v___x_1038_ = lean_array_uget_borrowed(v_as_1033_, v_i_1034_);
v_snd_1039_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_f_1032_);
v___x_1040_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_1032_, v_b_1036_, v_snd_1039_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1034_, v___x_1041_);
v_i_1034_ = v___x_1042_;
v_b_1036_ = v___x_1040_;
goto _start;
}
else
{
lean_dec(v_f_1032_);
return v_b_1036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg___boxed(lean_object* v_f_1044_, lean_object* v_as_1045_, lean_object* v_i_1046_, lean_object* v_stop_1047_, lean_object* v_b_1048_){
_start:
{
size_t v_i_boxed_1049_; size_t v_stop_boxed_1050_; lean_object* v_res_1051_; 
v_i_boxed_1049_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_stop_boxed_1050_ = lean_unbox_usize(v_stop_1047_);
lean_dec(v_stop_1047_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_1044_, v_as_1045_, v_i_boxed_1049_, v_stop_boxed_1050_, v_b_1048_);
lean_dec_ref(v_as_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg___boxed(lean_object* v_f_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_1052_, v_x_1053_, v_x_1054_);
lean_dec_ref(v_x_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(lean_object* v___f_1056_, lean_object* v_s_1057_, lean_object* v_x_1058_, lean_object* v_t_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v___f_1056_, v_s_1057_, v_t_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1___boxed(lean_object* v___f_1061_, lean_object* v_s_1062_, lean_object* v_x_1063_, lean_object* v_t_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(v___f_1061_, v_s_1062_, v_x_1063_, v_t_1064_);
lean_dec_ref(v_t_1064_);
lean_dec(v_x_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__2(lean_object* v_x1_1066_, lean_object* v_x2_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_array_push(v_x1_1066_, v_x2_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(lean_object* v___f_1069_, lean_object* v_s_1070_, lean_object* v_x_1071_, lean_object* v_t_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v___f_1069_, v_s_1070_, v_t_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3___boxed(lean_object* v___f_1074_, lean_object* v_s_1075_, lean_object* v_x_1076_, lean_object* v_t_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(v___f_1074_, v_s_1075_, v_x_1076_, v_t_1077_);
lean_dec_ref(v_t_1077_);
lean_dec(v_x_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v_ks_1083_; lean_object* v_vs_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1108_; 
v_ks_1083_ = lean_ctor_get(v_x_1079_, 0);
v_vs_1084_ = lean_ctor_get(v_x_1079_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_1079_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1086_ = v_x_1079_;
v_isShared_1087_ = v_isSharedCheck_1108_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_vs_1084_);
lean_inc(v_ks_1083_);
lean_dec(v_x_1079_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1108_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_array_get_size(v_ks_1083_);
v___x_1089_ = lean_nat_dec_lt(v_x_1080_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
lean_dec(v_x_1080_);
v___x_1090_ = lean_array_push(v_ks_1083_, v_x_1081_);
v___x_1091_ = lean_array_push(v_vs_1084_, v_x_1082_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v___x_1091_);
lean_ctor_set(v___x_1086_, 0, v___x_1090_);
v___x_1093_ = v___x_1086_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
else
{
lean_object* v_k_x27_1095_; uint8_t v___x_1096_; 
v_k_x27_1095_ = lean_array_fget_borrowed(v_ks_1083_, v_x_1080_);
lean_inc(v_k_x27_1095_);
lean_inc_ref(v_x_1081_);
v___x_1096_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1081_, v_k_x27_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1098_; 
if (v_isShared_1087_ == 0)
{
v___x_1098_ = v___x_1086_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_ks_1083_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_vs_1084_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_add(v_x_1080_, v___x_1099_);
lean_dec(v_x_1080_);
v_x_1079_ = v___x_1098_;
v_x_1080_ = v___x_1100_;
goto _start;
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1103_ = lean_array_fset(v_ks_1083_, v_x_1080_, v_x_1081_);
v___x_1104_ = lean_array_fset(v_vs_1084_, v_x_1080_, v_x_1082_);
lean_dec(v_x_1080_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v___x_1104_);
lean_ctor_set(v___x_1086_, 0, v___x_1103_);
v___x_1106_ = v___x_1086_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1109_, lean_object* v_k_1110_, lean_object* v_v_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(v_n_1109_, v___x_1112_, v_k_1110_, v_v_1111_);
return v___x_1113_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1114_; uint64_t v___x_1115_; 
v___x_1114_ = lean_unsigned_to_nat(1723u);
v___x_1115_ = lean_uint64_of_nat(v___x_1114_);
return v___x_1115_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; 
v___x_1116_ = ((size_t)5ULL);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_shift_left(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; 
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0);
v___x_1121_ = lean_usize_sub(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(lean_object* v_x_1123_, size_t v_x_1124_, size_t v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
lean_object* v_es_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v_j_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_es_1128_ = lean_ctor_get(v_x_1123_, 0);
v___x_1129_ = ((size_t)5ULL);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_1132_ = lean_usize_land(v_x_1124_, v___x_1131_);
v_j_1133_ = lean_usize_to_nat(v___x_1132_);
v___x_1134_ = lean_array_get_size(v_es_1128_);
v___x_1135_ = lean_nat_dec_lt(v_j_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_dec(v_j_1133_);
lean_dec(v_x_1127_);
lean_dec_ref(v_x_1126_);
return v_x_1123_;
}
else
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1172_; 
lean_inc_ref(v_es_1128_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_x_1123_, 0);
lean_dec(v_unused_1173_);
v___x_1137_ = v_x_1123_;
v_isShared_1138_ = v_isSharedCheck_1172_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v_x_1123_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1172_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_v_1139_; lean_object* v___x_1140_; lean_object* v_xs_x27_1141_; lean_object* v___y_1143_; 
v_v_1139_ = lean_array_fget(v_es_1128_, v_j_1133_);
v___x_1140_ = lean_box(0);
v_xs_x27_1141_ = lean_array_fset(v_es_1128_, v_j_1133_, v___x_1140_);
switch(lean_obj_tag(v_v_1139_))
{
case 0:
{
lean_object* v_key_1148_; lean_object* v_val_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_key_1148_ = lean_ctor_get(v_v_1139_, 0);
v_val_1149_ = lean_ctor_get(v_v_1139_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_v_1139_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1151_ = v_v_1139_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_val_1149_);
lean_inc(v_key_1148_);
lean_dec(v_v_1139_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; 
lean_inc(v_key_1148_);
lean_inc_ref(v_x_1126_);
v___x_1153_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_1126_, v_key_1148_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_del_object(v___x_1151_);
v___x_1154_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1148_, v_val_1149_, v_x_1126_, v_x_1127_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
v___y_1143_ = v___x_1155_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_val_1149_);
lean_dec(v_key_1148_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_x_1127_);
lean_ctor_set(v___x_1151_, 0, v_x_1126_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_x_1126_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_x_1127_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
v___y_1143_ = v___x_1157_;
goto v___jp_1142_;
}
}
}
}
case 1:
{
lean_object* v_node_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1170_; 
v_node_1160_ = lean_ctor_get(v_v_1139_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_v_1139_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1162_ = v_v_1139_;
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_node_1160_);
lean_dec(v_v_1139_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1164_ = lean_usize_shift_right(v_x_1124_, v___x_1129_);
v___x_1165_ = lean_usize_add(v_x_1125_, v___x_1130_);
v___x_1166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_node_1160_, v___x_1164_, v___x_1165_, v_x_1126_, v_x_1127_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1166_);
v___x_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v___y_1143_ = v___x_1168_;
goto v___jp_1142_;
}
}
}
default: 
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_x_1126_);
lean_ctor_set(v___x_1171_, 1, v_x_1127_);
v___y_1143_ = v___x_1171_;
goto v___jp_1142_;
}
}
v___jp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_array_fset(v_xs_x27_1141_, v_j_1133_, v___y_1143_);
lean_dec(v_j_1133_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1144_);
v___x_1146_ = v___x_1137_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v_ks_1174_; lean_object* v_vs_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1195_; 
v_ks_1174_ = lean_ctor_get(v_x_1123_, 0);
v_vs_1175_ = lean_ctor_get(v_x_1123_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1177_ = v_x_1123_;
v_isShared_1178_ = v_isSharedCheck_1195_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_vs_1175_);
lean_inc(v_ks_1174_);
lean_dec(v_x_1123_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1195_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_ks_1174_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_vs_1175_);
v___x_1180_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v_newNode_1181_; uint8_t v___y_1183_; size_t v___x_1189_; uint8_t v___x_1190_; 
v_newNode_1181_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v___x_1180_, v_x_1126_, v_x_1127_);
v___x_1189_ = ((size_t)7ULL);
v___x_1190_ = lean_usize_dec_le(v___x_1189_, v_x_1125_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1181_);
v___x_1192_ = lean_unsigned_to_nat(4u);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
lean_dec(v___x_1191_);
v___y_1183_ = v___x_1193_;
goto v___jp_1182_;
}
else
{
v___y_1183_ = v___x_1190_;
goto v___jp_1182_;
}
v___jp_1182_:
{
if (v___y_1183_ == 0)
{
lean_object* v_ks_1184_; lean_object* v_vs_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_ks_1184_ = lean_ctor_get(v_newNode_1181_, 0);
lean_inc_ref(v_ks_1184_);
v_vs_1185_ = lean_ctor_get(v_newNode_1181_, 1);
lean_inc_ref(v_vs_1185_);
lean_dec_ref(v_newNode_1181_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2);
v___x_1188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_x_1125_, v_ks_1184_, v_vs_1185_, v___x_1186_, v___x_1187_);
lean_dec_ref(v_vs_1185_);
lean_dec_ref(v_ks_1184_);
return v___x_1188_;
}
else
{
return v_newNode_1181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(size_t v_depth_1196_, lean_object* v_keys_1197_, lean_object* v_vals_1198_, lean_object* v_i_1199_, lean_object* v_entries_1200_){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_array_get_size(v_keys_1197_);
v___x_1202_ = lean_nat_dec_lt(v_i_1199_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v_i_1199_);
return v_entries_1200_;
}
else
{
lean_object* v_k_1203_; lean_object* v_v_1204_; uint64_t v___y_1206_; lean_object* v___x_1217_; 
v_k_1203_ = lean_array_fget_borrowed(v_keys_1197_, v_i_1199_);
v_v_1204_ = lean_array_fget_borrowed(v_vals_1198_, v_i_1199_);
v___x_1217_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_k_1203_);
if (lean_obj_tag(v___x_1217_) == 0)
{
uint64_t v___x_1218_; 
v___x_1218_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1206_ = v___x_1218_;
goto v___jp_1205_;
}
else
{
uint64_t v_hash_1219_; 
v_hash_1219_ = lean_ctor_get_uint64(v___x_1217_, sizeof(void*)*2);
lean_dec(v___x_1217_);
v___y_1206_ = v_hash_1219_;
goto v___jp_1205_;
}
v___jp_1205_:
{
size_t v_h_1207_; size_t v___x_1208_; lean_object* v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v_h_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_h_1207_ = lean_uint64_to_usize(v___y_1206_);
v___x_1208_ = ((size_t)5ULL);
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_sub(v_depth_1196_, v___x_1210_);
v___x_1212_ = lean_usize_mul(v___x_1208_, v___x_1211_);
v_h_1213_ = lean_usize_shift_right(v_h_1207_, v___x_1212_);
v___x_1214_ = lean_nat_add(v_i_1199_, v___x_1209_);
lean_dec(v_i_1199_);
lean_inc(v_v_1204_);
lean_inc(v_k_1203_);
v___x_1215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_entries_1200_, v_h_1213_, v_depth_1196_, v_k_1203_, v_v_1204_);
v_i_1199_ = v___x_1214_;
v_entries_1200_ = v___x_1215_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1220_, lean_object* v_keys_1221_, lean_object* v_vals_1222_, lean_object* v_i_1223_, lean_object* v_entries_1224_){
_start:
{
size_t v_depth_boxed_1225_; lean_object* v_res_1226_; 
v_depth_boxed_1225_ = lean_unbox_usize(v_depth_1220_);
lean_dec(v_depth_1220_);
v_res_1226_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1225_, v_keys_1221_, v_vals_1222_, v_i_1223_, v_entries_1224_);
lean_dec_ref(v_vals_1222_);
lean_dec_ref(v_keys_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___boxed(lean_object* v_x_1227_, lean_object* v_x_1228_, lean_object* v_x_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_){
_start:
{
size_t v_x_26612__boxed_1232_; size_t v_x_26613__boxed_1233_; lean_object* v_res_1234_; 
v_x_26612__boxed_1232_ = lean_unbox_usize(v_x_1228_);
lean_dec(v_x_1228_);
v_x_26613__boxed_1233_ = lean_unbox_usize(v_x_1229_);
lean_dec(v_x_1229_);
v_res_1234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_1227_, v_x_26612__boxed_1232_, v_x_26613__boxed_1233_, v_x_1230_, v_x_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(lean_object* v_x_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
uint64_t v___y_1239_; lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_1236_);
if (lean_obj_tag(v___x_1243_) == 0)
{
uint64_t v___x_1244_; 
v___x_1244_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1239_ = v___x_1244_;
goto v___jp_1238_;
}
else
{
uint64_t v_hash_1245_; 
v_hash_1245_ = lean_ctor_get_uint64(v___x_1243_, sizeof(void*)*2);
lean_dec(v___x_1243_);
v___y_1239_ = v_hash_1245_;
goto v___jp_1238_;
}
v___jp_1238_:
{
size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_uint64_to_usize(v___y_1239_);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_1235_, v___x_1240_, v___x_1241_, v_x_1236_, v_x_1237_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__4(lean_object* v_d_1246_, lean_object* v_a_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(v_a_1247_);
if (lean_obj_tag(v___x_1249_) == 0)
{
return v_d_1246_;
}
else
{
lean_object* v_val_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_val_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(v_d_1246_, v_val_1250_, v___x_1251_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0(lean_object* v_x_1253_, lean_object* v_keys_1254_, lean_object* v_v_1255_, lean_object* v_k_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v_c_1260_; lean_object* v___x_1261_; 
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_add(v_x_1253_, v___x_1258_);
v_c_1260_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1254_, v_v_1255_, v___x_1259_);
lean_dec(v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_k_1256_);
lean_ctor_set(v___x_1261_, 1, v_c_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0___boxed(lean_object* v_x_1262_, lean_object* v_keys_1263_, lean_object* v_v_1264_, lean_object* v_k_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0(v_x_1262_, v_keys_1263_, v_v_1264_, v_k_1265_, v_x_1266_);
lean_dec_ref(v_keys_1263_);
lean_dec(v_x_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(lean_object* v_a_1268_, lean_object* v_b_1269_){
_start:
{
lean_object* v_fst_1270_; lean_object* v_fst_1271_; uint8_t v___x_1272_; 
v_fst_1270_ = lean_ctor_get(v_a_1268_, 0);
v_fst_1271_ = lean_ctor_get(v_b_1269_, 0);
v___x_1272_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1270_, v_fst_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1___boxed(lean_object* v_a_1273_, lean_object* v_b_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v_a_1273_, v_b_1274_);
lean_dec_ref(v_b_1274_);
lean_dec_ref(v_a_1273_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(lean_object* v_vs_1277_, lean_object* v_v_1278_, lean_object* v_i_1279_){
_start:
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_array_get_size(v_vs_1277_);
v___x_1281_ = lean_nat_dec_lt(v_i_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_i_1279_);
v___x_1282_ = lean_array_push(v_vs_1277_, v_v_1278_);
return v___x_1282_;
}
else
{
lean_object* v_proof_1283_; lean_object* v___x_1284_; lean_object* v_proof_1285_; uint8_t v___x_1286_; 
v_proof_1283_ = lean_ctor_get(v_v_1278_, 1);
v___x_1284_ = lean_array_fget_borrowed(v_vs_1277_, v_i_1279_);
v_proof_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc_ref(v_proof_1285_);
lean_inc_ref(v_proof_1283_);
v___x_1286_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_1283_, v_proof_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v_i_1279_, v___x_1287_);
lean_dec(v_i_1279_);
v_i_1279_ = v___x_1288_;
goto _start;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_array_fset(v_vs_1277_, v_i_1279_, v_v_1278_);
lean_dec(v_i_1279_);
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(lean_object* v_vs_1291_, lean_object* v_v_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(v_vs_1291_, v_v_1292_, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg(lean_object* v_x_1299_, lean_object* v_keys_1300_, lean_object* v_v_1301_, lean_object* v_k_1302_, lean_object* v_as_1303_, lean_object* v_k_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_mid_1309_; lean_object* v_midVal_1310_; uint8_t v___x_1311_; 
v___x_1307_ = lean_nat_add(v_x_1305_, v_x_1306_);
v___x_1308_ = lean_unsigned_to_nat(1u);
v_mid_1309_ = lean_nat_shiftr(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
v_midVal_1310_ = lean_array_fget(v_as_1303_, v_mid_1309_);
v___x_1311_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v_midVal_1310_, v_k_1304_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; 
lean_dec(v_x_1306_);
v___x_1312_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v_k_1304_, v_midVal_1310_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
lean_dec(v_x_1305_);
v___x_1313_ = lean_array_get_size(v_as_1303_);
v___x_1314_ = lean_nat_dec_lt(v_mid_1309_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_dec(v_midVal_1310_);
lean_dec(v_mid_1309_);
lean_dec(v_k_1302_);
lean_dec_ref(v_v_1301_);
return v_as_1303_;
}
else
{
lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1327_; 
v_snd_1315_ = lean_ctor_get(v_midVal_1310_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_midVal_1310_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_midVal_1310_, 0);
lean_dec(v_unused_1328_);
v___x_1317_ = v_midVal_1310_;
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_dec(v_midVal_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v_xs_x27_1320_; lean_object* v___x_1321_; lean_object* v_c_1322_; lean_object* v___x_1324_; 
v___x_1319_ = lean_box(0);
v_xs_x27_1320_ = lean_array_fset(v_as_1303_, v_mid_1309_, v___x_1319_);
v___x_1321_ = lean_nat_add(v_x_1299_, v___x_1308_);
v_c_1322_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(v_keys_1300_, v_v_1301_, v___x_1321_, v_snd_1315_);
lean_dec(v___x_1321_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_c_1322_);
lean_ctor_set(v___x_1317_, 0, v_k_1302_);
v___x_1324_ = v___x_1317_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_k_1302_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_c_1322_);
v___x_1324_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_array_fset(v_xs_x27_1320_, v_mid_1309_, v___x_1324_);
lean_dec(v_mid_1309_);
return v___x_1325_;
}
}
}
}
else
{
lean_dec(v_midVal_1310_);
v_x_1306_ = v_mid_1309_;
goto _start;
}
}
else
{
uint8_t v___x_1330_; 
lean_dec(v_midVal_1310_);
v___x_1330_ = lean_nat_dec_eq(v_mid_1309_, v_x_1305_);
if (v___x_1330_ == 0)
{
lean_dec(v_x_1305_);
v_x_1305_ = v_mid_1309_;
goto _start;
}
else
{
lean_object* v___x_1332_; lean_object* v_c_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_j_1336_; lean_object* v_as_1337_; lean_object* v___x_1338_; 
lean_dec(v_mid_1309_);
lean_dec(v_x_1306_);
v___x_1332_ = lean_nat_add(v_x_1299_, v___x_1308_);
v_c_1333_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1300_, v_v_1301_, v___x_1332_);
lean_dec(v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_k_1302_);
lean_ctor_set(v___x_1334_, 1, v_c_1333_);
v___x_1335_ = lean_nat_add(v_x_1305_, v___x_1308_);
lean_dec(v_x_1305_);
v_j_1336_ = lean_array_get_size(v_as_1303_);
v_as_1337_ = lean_array_push(v_as_1303_, v___x_1334_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1335_, v_as_1337_, v_j_1336_);
lean_dec(v___x_1335_);
return v___x_1338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18(lean_object* v_x_1339_, lean_object* v_keys_1340_, lean_object* v_v_1341_, lean_object* v_k_1342_, lean_object* v_as_1343_, lean_object* v_k_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1345_ = lean_array_get_size(v_as_1343_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_nat_dec_eq(v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_array_fget_borrowed(v_as_1343_, v___x_1346_);
v___x_1349_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v_k_1344_, v___x_1348_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v___x_1348_, v_k_1344_);
if (v___x_1350_ == 0)
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_nat_dec_lt(v___x_1346_, v___x_1345_);
if (v___x_1351_ == 0)
{
lean_dec(v_k_1342_);
lean_dec_ref(v_v_1341_);
return v_as_1343_;
}
else
{
lean_object* v___x_1352_; lean_object* v_xs_x27_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_inc(v___x_1348_);
v___x_1352_ = lean_box(0);
v_xs_x27_1353_ = lean_array_fset(v_as_1343_, v___x_1346_, v___x_1352_);
v___x_1354_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2(v_x_1339_, v_keys_1340_, v_v_1341_, v_k_1342_, v___x_1348_);
v___x_1355_ = lean_array_fset(v_xs_x27_1353_, v___x_1346_, v___x_1354_);
return v___x_1355_;
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_sub(v___x_1345_, v___x_1356_);
v___x_1358_ = lean_array_fget_borrowed(v_as_1343_, v___x_1357_);
v___x_1359_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v___x_1358_, v_k_1344_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__1(v_k_1344_, v___x_1358_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_nat_dec_lt(v___x_1357_, v___x_1345_);
if (v___x_1361_ == 0)
{
lean_dec(v___x_1357_);
lean_dec(v_k_1342_);
lean_dec_ref(v_v_1341_);
return v_as_1343_;
}
else
{
lean_object* v___x_1362_; lean_object* v_xs_x27_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_inc(v___x_1358_);
v___x_1362_ = lean_box(0);
v_xs_x27_1363_ = lean_array_fset(v_as_1343_, v___x_1357_, v___x_1362_);
v___x_1364_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2(v_x_1339_, v_keys_1340_, v_v_1341_, v_k_1342_, v___x_1358_);
v___x_1365_ = lean_array_fset(v_xs_x27_1363_, v___x_1357_, v___x_1364_);
lean_dec(v___x_1357_);
return v___x_1365_;
}
}
else
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg(v_x_1339_, v_keys_1340_, v_v_1341_, v_k_1342_, v_as_1343_, v_k_1344_, v___x_1346_, v___x_1357_);
return v___x_1366_;
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v___x_1357_);
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0(v_x_1339_, v_keys_1340_, v_v_1341_, v_k_1342_, v___x_1367_);
v___x_1369_ = lean_array_push(v_as_1343_, v___x_1368_);
return v___x_1369_;
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_as_1372_; lean_object* v___x_1373_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0(v_x_1339_, v_keys_1340_, v_v_1341_, v_k_1342_, v___x_1370_);
v_as_1372_ = lean_array_push(v_as_1343_, v___x_1371_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1346_, v_as_1372_, v___x_1345_);
return v___x_1373_;
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__0(v_x_1339_, v_keys_1340_, v_v_1341_, v_k_1342_, v___x_1374_);
v___x_1376_ = lean_array_push(v_as_1343_, v___x_1375_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(lean_object* v_keys_1377_, lean_object* v_v_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_vs_1381_; lean_object* v_children_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1399_; 
v_vs_1381_ = lean_ctor_get(v_x_1380_, 0);
v_children_1382_ = lean_ctor_get(v_x_1380_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1380_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1384_ = v_x_1380_;
v_isShared_1385_ = v_isSharedCheck_1399_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_children_1382_);
lean_inc(v_vs_1381_);
lean_dec(v_x_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1399_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = lean_array_get_size(v_keys_1377_);
v___x_1387_ = lean_nat_dec_lt(v_x_1379_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(v_vs_1381_, v_v_1378_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_children_1382_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_object* v_k_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_c_1395_; lean_object* v___x_1397_; 
v_k_1392_ = lean_array_fget_borrowed(v_keys_1377_, v_x_1379_);
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__1));
lean_inc_n(v_k_1392_, 2);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_k_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v_c_1395_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18(v_x_1379_, v_keys_1377_, v_v_1378_, v_k_1392_, v_children_1382_, v___x_1394_);
lean_dec_ref_known(v___x_1394_, 2);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v_c_1395_);
v___x_1397_ = v___x_1384_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_vs_1381_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_c_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2(lean_object* v_x_1400_, lean_object* v_keys_1401_, lean_object* v_v_1402_, lean_object* v_k_1403_, lean_object* v_x_1404_){
_start:
{
lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1415_; 
v_snd_1405_ = lean_ctor_get(v_x_1404_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_x_1404_, 0);
lean_dec(v_unused_1416_);
v___x_1407_ = v_x_1404_;
v_isShared_1408_ = v_isSharedCheck_1415_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_dec(v_x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1415_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_c_1411_; lean_object* v___x_1413_; 
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_add(v_x_1400_, v___x_1409_);
v_c_1411_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(v_keys_1401_, v_v_1402_, v___x_1410_, v_snd_1405_);
lean_dec(v___x_1410_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v_c_1411_);
lean_ctor_set(v___x_1407_, 0, v_k_1403_);
v___x_1413_ = v___x_1407_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_k_1403_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_c_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2___boxed(lean_object* v_x_1417_, lean_object* v_keys_1418_, lean_object* v_v_1419_, lean_object* v_k_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___lam__2(v_x_1417_, v_keys_1418_, v_v_1419_, v_k_1420_, v_x_1421_);
lean_dec_ref(v_keys_1418_);
lean_dec(v_x_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___boxed(lean_object* v_keys_1423_, lean_object* v_v_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(v_keys_1423_, v_v_1424_, v_x_1425_, v_x_1426_);
lean_dec(v_x_1425_);
lean_dec_ref(v_keys_1423_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg___boxed(lean_object* v_x_1428_, lean_object* v_keys_1429_, lean_object* v_v_1430_, lean_object* v_k_1431_, lean_object* v_as_1432_, lean_object* v_k_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg(v_x_1428_, v_keys_1429_, v_v_1430_, v_k_1431_, v_as_1432_, v_k_1433_, v_x_1434_, v_x_1435_);
lean_dec_ref(v_k_1433_);
lean_dec_ref(v_keys_1429_);
lean_dec(v_x_1428_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18___boxed(lean_object* v_x_1437_, lean_object* v_keys_1438_, lean_object* v_v_1439_, lean_object* v_k_1440_, lean_object* v_as_1441_, lean_object* v_k_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18(v_x_1437_, v_keys_1438_, v_v_1439_, v_k_1440_, v_as_1441_, v_k_1442_);
lean_dec_ref(v_k_1442_);
lean_dec_ref(v_keys_1438_);
lean_dec(v_x_1437_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(lean_object* v_keys_1444_, lean_object* v_v_1445_, lean_object* v_x_1446_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1444_, v_v_1445_, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
else
{
lean_object* v_val_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1459_; 
v_val_1450_ = lean_ctor_get(v_x_1446_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_x_1446_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1452_ = v_x_1446_;
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_val_1450_);
lean_dec(v_x_1446_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(v_keys_1444_, v_v_1445_, v___x_1454_, v_val_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0___boxed(lean_object* v_keys_1460_, lean_object* v_v_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(v_keys_1460_, v_v_1461_, v_x_1462_);
lean_dec_ref(v_keys_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20_spec__30(lean_object* v_xs_1464_, lean_object* v_v_1465_, lean_object* v_i_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_array_get_size(v_xs_1464_);
v___x_1468_ = lean_nat_dec_lt(v_i_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_i_1466_);
v___x_1469_ = lean_box(0);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_array_fget_borrowed(v_xs_1464_, v_i_1466_);
v___x_1471_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_1470_, v_v_1465_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v_i_1466_, v___x_1472_);
lean_dec(v_i_1466_);
v_i_1466_ = v___x_1473_;
goto _start;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_i_1466_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20_spec__30___boxed(lean_object* v_xs_1476_, lean_object* v_v_1477_, lean_object* v_i_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20_spec__30(v_xs_1476_, v_v_1477_, v_i_1478_);
lean_dec(v_v_1477_);
lean_dec_ref(v_xs_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20(lean_object* v_xs_1480_, lean_object* v_v_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20_spec__30(v_xs_1480_, v_v_1481_, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20___boxed(lean_object* v_xs_1484_, lean_object* v_v_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20(v_xs_1484_, v_v_1485_);
lean_dec(v_v_1485_);
lean_dec_ref(v_xs_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32_spec__37___redArg(lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v_ks_1491_; lean_object* v_vs_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1516_; 
v_ks_1491_ = lean_ctor_get(v_x_1487_, 0);
v_vs_1492_ = lean_ctor_get(v_x_1487_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_x_1487_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1494_ = v_x_1487_;
v_isShared_1495_ = v_isSharedCheck_1516_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_vs_1492_);
lean_inc(v_ks_1491_);
lean_dec(v_x_1487_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1516_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = lean_array_get_size(v_ks_1491_);
v___x_1497_ = lean_nat_dec_lt(v_x_1488_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec(v_x_1488_);
v___x_1498_ = lean_array_push(v_ks_1491_, v_x_1489_);
v___x_1499_ = lean_array_push(v_vs_1492_, v_x_1490_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1499_);
lean_ctor_set(v___x_1494_, 0, v___x_1498_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
else
{
lean_object* v_k_x27_1503_; uint8_t v___x_1504_; 
v_k_x27_1503_ = lean_array_fget_borrowed(v_ks_1491_, v_x_1488_);
v___x_1504_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1489_, v_k_x27_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1506_; 
if (v_isShared_1495_ == 0)
{
v___x_1506_ = v___x_1494_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_ks_1491_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_vs_1492_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_nat_add(v_x_1488_, v___x_1507_);
lean_dec(v_x_1488_);
v_x_1487_ = v___x_1506_;
v_x_1488_ = v___x_1508_;
goto _start;
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1511_ = lean_array_fset(v_ks_1491_, v_x_1488_, v_x_1489_);
v___x_1512_ = lean_array_fset(v_vs_1492_, v_x_1488_, v_x_1490_);
lean_dec(v_x_1488_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1512_);
lean_ctor_set(v___x_1494_, 0, v___x_1511_);
v___x_1514_ = v___x_1494_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32___redArg(lean_object* v_n_1517_, lean_object* v_k_1518_, lean_object* v_v_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32_spec__37___redArg(v_n_1517_, v___x_1520_, v_k_1518_, v_v_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___closed__0(void){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(lean_object* v_x_1523_, size_t v_x_1524_, size_t v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1523_) == 0)
{
lean_object* v_es_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; lean_object* v_j_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_es_1528_ = lean_ctor_get(v_x_1523_, 0);
v___x_1529_ = ((size_t)5ULL);
v___x_1530_ = ((size_t)1ULL);
v___x_1531_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_1532_ = lean_usize_land(v_x_1524_, v___x_1531_);
v_j_1533_ = lean_usize_to_nat(v___x_1532_);
v___x_1534_ = lean_array_get_size(v_es_1528_);
v___x_1535_ = lean_nat_dec_lt(v_j_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_dec(v_j_1533_);
lean_dec(v_x_1527_);
lean_dec(v_x_1526_);
return v_x_1523_;
}
else
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1572_; 
lean_inc_ref(v_es_1528_);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1573_);
v___x_1537_ = v_x_1523_;
v_isShared_1538_ = v_isSharedCheck_1572_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v_x_1523_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1572_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_v_1539_; lean_object* v___x_1540_; lean_object* v_xs_x27_1541_; lean_object* v___y_1543_; 
v_v_1539_ = lean_array_fget(v_es_1528_, v_j_1533_);
v___x_1540_ = lean_box(0);
v_xs_x27_1541_ = lean_array_fset(v_es_1528_, v_j_1533_, v___x_1540_);
switch(lean_obj_tag(v_v_1539_))
{
case 0:
{
lean_object* v_key_1548_; lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1559_; 
v_key_1548_ = lean_ctor_get(v_v_1539_, 0);
v_val_1549_ = lean_ctor_get(v_v_1539_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_v_1539_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1551_ = v_v_1539_;
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_inc(v_key_1548_);
lean_dec(v_v_1539_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; 
v___x_1553_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1526_, v_key_1548_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_del_object(v___x_1551_);
v___x_1554_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1548_, v_val_1549_, v_x_1526_, v_x_1527_);
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
v___y_1543_ = v___x_1555_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1557_; 
lean_dec(v_val_1549_);
lean_dec(v_key_1548_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v_x_1527_);
lean_ctor_set(v___x_1551_, 0, v_x_1526_);
v___x_1557_ = v___x_1551_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_x_1526_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_x_1527_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
v___y_1543_ = v___x_1557_;
goto v___jp_1542_;
}
}
}
}
case 1:
{
lean_object* v_node_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1570_; 
v_node_1560_ = lean_ctor_get(v_v_1539_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_v_1539_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1562_ = v_v_1539_;
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_node_1560_);
lean_dec(v_v_1539_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1564_ = lean_usize_shift_right(v_x_1524_, v___x_1529_);
v___x_1565_ = lean_usize_add(v_x_1525_, v___x_1530_);
v___x_1566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(v_node_1560_, v___x_1564_, v___x_1565_, v_x_1526_, v_x_1527_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1566_);
v___x_1568_ = v___x_1562_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
v___y_1543_ = v___x_1568_;
goto v___jp_1542_;
}
}
}
default: 
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_x_1526_);
lean_ctor_set(v___x_1571_, 1, v_x_1527_);
v___y_1543_ = v___x_1571_;
goto v___jp_1542_;
}
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = lean_array_fset(v_xs_x27_1541_, v_j_1533_, v___y_1543_);
lean_dec(v_j_1533_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1544_);
v___x_1546_ = v___x_1537_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
else
{
lean_object* v_ks_1574_; lean_object* v_vs_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1595_; 
v_ks_1574_ = lean_ctor_get(v_x_1523_, 0);
v_vs_1575_ = lean_ctor_get(v_x_1523_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1577_ = v_x_1523_;
v_isShared_1578_ = v_isSharedCheck_1595_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_vs_1575_);
lean_inc(v_ks_1574_);
lean_dec(v_x_1523_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1595_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_ks_1574_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_vs_1575_);
v___x_1580_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v_newNode_1581_; uint8_t v___y_1583_; size_t v___x_1589_; uint8_t v___x_1590_; 
v_newNode_1581_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32___redArg(v___x_1580_, v_x_1526_, v_x_1527_);
v___x_1589_ = ((size_t)7ULL);
v___x_1590_ = lean_usize_dec_le(v___x_1589_, v_x_1525_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1581_);
v___x_1592_ = lean_unsigned_to_nat(4u);
v___x_1593_ = lean_nat_dec_lt(v___x_1591_, v___x_1592_);
lean_dec(v___x_1591_);
v___y_1583_ = v___x_1593_;
goto v___jp_1582_;
}
else
{
v___y_1583_ = v___x_1590_;
goto v___jp_1582_;
}
v___jp_1582_:
{
if (v___y_1583_ == 0)
{
lean_object* v_ks_1584_; lean_object* v_vs_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_ks_1584_ = lean_ctor_get(v_newNode_1581_, 0);
lean_inc_ref(v_ks_1584_);
v_vs_1585_ = lean_ctor_get(v_newNode_1581_, 1);
lean_inc_ref(v_vs_1585_);
lean_dec_ref(v_newNode_1581_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___closed__0);
v___x_1588_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg(v_x_1525_, v_ks_1584_, v_vs_1585_, v___x_1586_, v___x_1587_);
lean_dec_ref(v_vs_1585_);
lean_dec_ref(v_ks_1584_);
return v___x_1588_;
}
else
{
return v_newNode_1581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg(size_t v_depth_1596_, lean_object* v_keys_1597_, lean_object* v_vals_1598_, lean_object* v_i_1599_, lean_object* v_entries_1600_){
_start:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = lean_array_get_size(v_keys_1597_);
v___x_1602_ = lean_nat_dec_lt(v_i_1599_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_dec(v_i_1599_);
return v_entries_1600_;
}
else
{
lean_object* v_k_1603_; lean_object* v_v_1604_; uint64_t v___x_1605_; size_t v_h_1606_; size_t v___x_1607_; lean_object* v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; size_t v_h_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_k_1603_ = lean_array_fget_borrowed(v_keys_1597_, v_i_1599_);
v_v_1604_ = lean_array_fget_borrowed(v_vals_1598_, v_i_1599_);
v___x_1605_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1603_);
v_h_1606_ = lean_uint64_to_usize(v___x_1605_);
v___x_1607_ = ((size_t)5ULL);
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_sub(v_depth_1596_, v___x_1609_);
v___x_1611_ = lean_usize_mul(v___x_1607_, v___x_1610_);
v_h_1612_ = lean_usize_shift_right(v_h_1606_, v___x_1611_);
v___x_1613_ = lean_nat_add(v_i_1599_, v___x_1608_);
lean_dec(v_i_1599_);
lean_inc(v_v_1604_);
lean_inc(v_k_1603_);
v___x_1614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(v_entries_1600_, v_h_1612_, v_depth_1596_, v_k_1603_, v_v_1604_);
v_i_1599_ = v___x_1613_;
v_entries_1600_ = v___x_1614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg___boxed(lean_object* v_depth_1616_, lean_object* v_keys_1617_, lean_object* v_vals_1618_, lean_object* v_i_1619_, lean_object* v_entries_1620_){
_start:
{
size_t v_depth_boxed_1621_; lean_object* v_res_1622_; 
v_depth_boxed_1621_ = lean_unbox_usize(v_depth_1616_);
lean_dec(v_depth_1616_);
v_res_1622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg(v_depth_boxed_1621_, v_keys_1617_, v_vals_1618_, v_i_1619_, v_entries_1620_);
lean_dec_ref(v_vals_1618_);
lean_dec_ref(v_keys_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg___boxed(lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
size_t v_x_27185__boxed_1628_; size_t v_x_27186__boxed_1629_; lean_object* v_res_1630_; 
v_x_27185__boxed_1628_ = lean_unbox_usize(v_x_1624_);
lean_dec(v_x_1624_);
v_x_27186__boxed_1629_ = lean_unbox_usize(v_x_1625_);
lean_dec(v_x_1625_);
v_res_1630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(v_x_1623_, v_x_27185__boxed_1628_, v_x_27186__boxed_1629_, v_x_1626_, v_x_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(lean_object* v_keys_1631_, lean_object* v_v_1632_, lean_object* v_x_1633_, size_t v_x_1634_, size_t v_x_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 0)
{
lean_object* v_es_1637_; size_t v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; size_t v___x_1641_; lean_object* v_j_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v_es_1637_ = lean_ctor_get(v_x_1633_, 0);
v___x_1638_ = ((size_t)5ULL);
v___x_1639_ = ((size_t)1ULL);
v___x_1640_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_1641_ = lean_usize_land(v_x_1634_, v___x_1640_);
v_j_1642_ = lean_usize_to_nat(v___x_1641_);
v___x_1643_ = lean_array_get_size(v_es_1637_);
v___x_1644_ = lean_nat_dec_lt(v_j_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_dec(v_j_1642_);
lean_dec(v_x_1636_);
lean_dec_ref(v_v_1632_);
return v_x_1633_;
}
else
{
lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1710_; 
lean_inc_ref(v_es_1637_);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_x_1633_, 0);
lean_dec(v_unused_1711_);
v___x_1646_ = v_x_1633_;
v_isShared_1647_ = v_isSharedCheck_1710_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v_x_1633_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1710_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_v_1648_; lean_object* v___x_1649_; lean_object* v_xs_x27_1650_; lean_object* v___y_1652_; 
v_v_1648_ = lean_array_fget(v_es_1637_, v_j_1642_);
v___x_1649_ = lean_box(0);
v_xs_x27_1650_ = lean_array_fset(v_es_1637_, v_j_1642_, v___x_1649_);
switch(lean_obj_tag(v_v_1648_))
{
case 0:
{
lean_object* v_key_1657_; lean_object* v_val_1658_; uint8_t v___x_1659_; 
v_key_1657_ = lean_ctor_get(v_v_1648_, 0);
v_val_1658_ = lean_ctor_get(v_v_1648_, 1);
v___x_1659_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1636_, v_key_1657_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(v_keys_1631_, v_v_1632_, v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec(v_x_1636_);
v___y_1652_ = v_v_1648_;
goto v___jp_1651_;
}
else
{
lean_object* v_val_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1670_; 
lean_inc(v_val_1658_);
lean_inc(v_key_1657_);
lean_dec_ref_known(v_v_1648_, 2);
v_val_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_val_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1657_, v_val_1658_, v_x_1636_, v_val_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v___y_1652_ = v___x_1668_;
goto v___jp_1651_;
}
}
}
}
else
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1681_; 
lean_inc(v_val_1658_);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_v_1648_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1682_ = lean_ctor_get(v_v_1648_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_v_1648_, 0);
lean_dec(v_unused_1683_);
v___x_1672_ = v_v_1648_;
v_isShared_1673_ = v_isSharedCheck_1681_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v_v_1648_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1681_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_val_1658_);
v___x_1675_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(v_keys_1631_, v_v_1632_, v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
lean_del_object(v___x_1672_);
lean_dec(v_x_1636_);
v___x_1676_ = lean_box(2);
v___y_1652_ = v___x_1676_;
goto v___jp_1651_;
}
else
{
lean_object* v_val_1677_; lean_object* v___x_1679_; 
v_val_1677_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v___x_1675_, 1);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v_val_1677_);
lean_ctor_set(v___x_1672_, 0, v_x_1636_);
v___x_1679_ = v___x_1672_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_x_1636_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_val_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
v___y_1652_ = v___x_1679_;
goto v___jp_1651_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1705_; 
v_node_1684_ = lean_ctor_get(v_v_1648_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_v_1648_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1686_ = v_v_1648_;
v_isShared_1687_ = v_isSharedCheck_1705_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_node_1684_);
lean_dec(v_v_1648_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1705_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
size_t v___x_1688_; size_t v___x_1689_; lean_object* v_newNode_1690_; lean_object* v___x_1691_; 
v___x_1688_ = lean_usize_shift_right(v_x_1634_, v___x_1638_);
v___x_1689_ = lean_usize_add(v_x_1635_, v___x_1639_);
v_newNode_1690_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(v_keys_1631_, v_v_1632_, v_node_1684_, v___x_1688_, v___x_1689_, v_x_1636_);
lean_inc_ref(v_newNode_1690_);
v___x_1691_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1690_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1693_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v_newNode_1690_);
v___x_1693_ = v___x_1686_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_newNode_1690_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v___y_1652_ = v___x_1693_;
goto v___jp_1651_;
}
}
else
{
lean_object* v_val_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_newNode_1690_);
lean_del_object(v___x_1686_);
v_val_1695_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_val_1695_);
lean_dec_ref_known(v___x_1691_, 1);
v_fst_1696_ = lean_ctor_get(v_val_1695_, 0);
v_snd_1697_ = lean_ctor_get(v_val_1695_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_val_1695_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v_val_1695_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snd_1697_);
lean_inc(v_fst_1696_);
lean_dec(v_val_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_fst_1696_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_snd_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
v___y_1652_ = v___x_1702_;
goto v___jp_1651_;
}
}
}
}
}
default: 
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(v_keys_1631_, v_v_1632_, v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec(v_x_1636_);
v___y_1652_ = v_v_1648_;
goto v___jp_1651_;
}
else
{
lean_object* v_val_1708_; lean_object* v___x_1709_; 
v_val_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_x_1636_);
lean_ctor_set(v___x_1709_, 1, v_val_1708_);
v___y_1652_ = v___x_1709_;
goto v___jp_1651_;
}
}
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = lean_array_fset(v_xs_x27_1650_, v_j_1642_, v___y_1652_);
lean_dec(v_j_1642_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1653_);
v___x_1655_ = v___x_1646_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
else
{
lean_object* v_ks_1712_; lean_object* v_vs_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1746_; 
v_ks_1712_ = lean_ctor_get(v_x_1633_, 0);
v_vs_1713_ = lean_ctor_get(v_x_1633_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1715_ = v_x_1633_;
v_isShared_1716_ = v_isSharedCheck_1746_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_vs_1713_);
lean_inc(v_ks_1712_);
lean_dec(v_x_1633_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1746_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__20(v_ks_1712_, v_x_1636_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1719_; 
if (v_isShared_1716_ == 0)
{
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_ks_1712_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_vs_1713_);
v___x_1719_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(v_keys_1631_, v_v_1632_, v___x_1720_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_dec(v_x_1636_);
return v___x_1719_;
}
else
{
lean_object* v_val_1722_; lean_object* v___x_1723_; 
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(v___x_1719_, v_x_1634_, v_x_1635_, v_x_1636_, v_val_1722_);
return v___x_1723_;
}
}
}
else
{
lean_object* v_val_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1745_; 
v_val_1725_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1727_ = v___x_1717_;
v_isShared_1728_ = v_isSharedCheck_1745_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_val_1725_);
lean_dec(v___x_1717_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1745_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_v_x27_1729_; lean_object* v_keys_1730_; lean_object* v_vals_1731_; lean_object* v___x_1733_; 
v_v_x27_1729_ = lean_array_fget(v_vs_1713_, v_val_1725_);
lean_inc(v_val_1725_);
v_keys_1730_ = l_Array_eraseIdx___redArg(v_ks_1712_, v_val_1725_);
v_vals_1731_ = l_Array_eraseIdx___redArg(v_vs_1713_, v_val_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_v_x27_1729_);
v___x_1733_ = v___x_1727_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_v_x27_1729_);
v___x_1733_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___lam__0(v_keys_1631_, v_v_1632_, v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1736_; 
lean_dec(v_x_1636_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_vals_1731_);
lean_ctor_set(v___x_1715_, 0, v_keys_1730_);
v___x_1736_ = v___x_1715_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_keys_1730_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_vals_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v_val_1738_; lean_object* v_keys_1739_; lean_object* v_vals_1740_; lean_object* v___x_1742_; 
v_val_1738_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v___x_1734_, 1);
v_keys_1739_ = lean_array_push(v_keys_1730_, v_x_1636_);
v_vals_1740_ = lean_array_push(v_vals_1731_, v_val_1738_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_vals_1740_);
lean_ctor_set(v___x_1715_, 0, v_keys_1739_);
v___x_1742_ = v___x_1715_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_keys_1739_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_vals_1740_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___boxed(lean_object* v_keys_1747_, lean_object* v_v_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
size_t v_x_27347__boxed_1753_; size_t v_x_27348__boxed_1754_; lean_object* v_res_1755_; 
v_x_27347__boxed_1753_ = lean_unbox_usize(v_x_1750_);
lean_dec(v_x_1750_);
v_x_27348__boxed_1754_ = lean_unbox_usize(v_x_1751_);
lean_dec(v_x_1751_);
v_res_1755_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(v_keys_1747_, v_v_1748_, v_x_1749_, v_x_27347__boxed_1753_, v_x_27348__boxed_1754_, v_x_1752_);
lean_dec_ref(v_keys_1747_);
return v_res_1755_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object* v_msg_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0);
v___x_1759_ = lean_panic_fn_borrowed(v___x_1758_, v_msg_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1763_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2));
v___x_1764_ = lean_unsigned_to_nat(23u);
v___x_1765_ = lean_unsigned_to_nat(166u);
v___x_1766_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1));
v___x_1767_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0));
v___x_1768_ = l_mkPanicMessageWithDecl(v___x_1767_, v___x_1766_, v___x_1765_, v___x_1764_, v___x_1763_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(lean_object* v_d_1769_, lean_object* v_keys_1770_, lean_object* v_v_1771_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = lean_array_get_size(v_keys_1770_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_nat_dec_eq(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v_k_1776_; uint64_t v___x_1777_; size_t v_h_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1775_ = lean_box(0);
v_k_1776_ = lean_array_get_borrowed(v___x_1775_, v_keys_1770_, v___x_1773_);
v___x_1777_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1776_);
v_h_1778_ = lean_uint64_to_usize(v___x_1777_);
v___x_1779_ = ((size_t)1ULL);
lean_inc(v_k_1776_);
v___x_1780_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(v_keys_1770_, v_v_1771_, v_d_1769_, v_h_1778_, v___x_1779_, v_k_1776_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v_v_1771_);
lean_dec_ref(v_d_1769_);
v___x_1781_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3);
v___x_1782_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v___x_1781_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(lean_object* v_d_1783_, lean_object* v_keys_1784_, lean_object* v_v_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_d_1783_, v_keys_1784_, v_v_1785_);
lean_dec_ref(v_keys_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(lean_object* v_d_1787_, lean_object* v_p_1788_, lean_object* v_v_1789_){
_start:
{
lean_object* v_keys_1790_; lean_object* v___x_1791_; 
v_keys_1790_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_1788_);
v___x_1791_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_d_1787_, v_keys_1790_, v_v_1789_);
lean_dec_ref(v_keys_1790_);
return v___x_1791_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1792_; double v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_float_of_nat(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(lean_object* v_cls_1797_, lean_object* v_msg_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1850_; 
v_ref_1804_ = lean_ctor_get(v___y_1801_, 5);
v___x_1805_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1850_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1850_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v_traceState_1811_; lean_object* v_env_1812_; lean_object* v_nextMacroScope_1813_; lean_object* v_ngen_1814_; lean_object* v_auxDeclNGen_1815_; lean_object* v_cache_1816_; lean_object* v_messages_1817_; lean_object* v_infoState_1818_; lean_object* v_snapshotTasks_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1849_; 
v___x_1810_ = lean_st_ref_take(v___y_1802_);
v_traceState_1811_ = lean_ctor_get(v___x_1810_, 4);
v_env_1812_ = lean_ctor_get(v___x_1810_, 0);
v_nextMacroScope_1813_ = lean_ctor_get(v___x_1810_, 1);
v_ngen_1814_ = lean_ctor_get(v___x_1810_, 2);
v_auxDeclNGen_1815_ = lean_ctor_get(v___x_1810_, 3);
v_cache_1816_ = lean_ctor_get(v___x_1810_, 5);
v_messages_1817_ = lean_ctor_get(v___x_1810_, 6);
v_infoState_1818_ = lean_ctor_get(v___x_1810_, 7);
v_snapshotTasks_1819_ = lean_ctor_get(v___x_1810_, 8);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1821_ = v___x_1810_;
v_isShared_1822_ = v_isSharedCheck_1849_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snapshotTasks_1819_);
lean_inc(v_infoState_1818_);
lean_inc(v_messages_1817_);
lean_inc(v_cache_1816_);
lean_inc(v_traceState_1811_);
lean_inc(v_auxDeclNGen_1815_);
lean_inc(v_ngen_1814_);
lean_inc(v_nextMacroScope_1813_);
lean_inc(v_env_1812_);
lean_dec(v___x_1810_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1849_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint64_t v_tid_1823_; lean_object* v_traces_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1848_; 
v_tid_1823_ = lean_ctor_get_uint64(v_traceState_1811_, sizeof(void*)*1);
v_traces_1824_ = lean_ctor_get(v_traceState_1811_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_traceState_1811_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1826_ = v_traceState_1811_;
v_isShared_1827_ = v_isSharedCheck_1848_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_traces_1824_);
lean_dec(v_traceState_1811_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1848_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; double v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0);
v___x_1830_ = 0;
v___x_1831_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1));
v___x_1832_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1832_, 0, v_cls_1797_);
lean_ctor_set(v___x_1832_, 1, v___x_1828_);
lean_ctor_set(v___x_1832_, 2, v___x_1831_);
lean_ctor_set_float(v___x_1832_, sizeof(void*)*3, v___x_1829_);
lean_ctor_set_float(v___x_1832_, sizeof(void*)*3 + 8, v___x_1829_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*3 + 16, v___x_1830_);
v___x_1833_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2));
v___x_1834_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v_a_1806_);
lean_ctor_set(v___x_1834_, 2, v___x_1833_);
lean_inc(v_ref_1804_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_ref_1804_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_PersistentArray_push___redArg(v_traces_1824_, v___x_1835_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1836_);
v___x_1838_ = v___x_1826_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1836_);
lean_ctor_set_uint64(v_reuseFailAlloc_1847_, sizeof(void*)*1, v_tid_1823_);
v___x_1838_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 4, v___x_1838_);
v___x_1840_ = v___x_1821_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_env_1812_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_nextMacroScope_1813_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_ngen_1814_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_auxDeclNGen_1815_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_cache_1816_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_messages_1817_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_infoState_1818_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_snapshotTasks_1819_);
v___x_1840_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_st_ref_set(v___y_1802_, v___x_1840_);
v___x_1842_ = lean_box(0);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1842_);
v___x_1844_ = v___x_1808_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___boxed(lean_object* v_cls_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5));
v___x_1872_ = l_Lean_Name_append(v___x_1871_, v___x_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7));
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9));
v___x_1878_ = l_Lean_stringToMessageData(v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(lean_object* v_as_1879_, size_t v_sz_1880_, size_t v_i_1881_, lean_object* v_b_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_a_1891_; uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_lt(v_i_1881_, v_sz_1880_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_b_1882_);
return v___x_1896_;
}
else
{
lean_object* v_a_1897_; lean_object* v_origin_1898_; 
v_a_1897_ = lean_array_uget_borrowed(v_as_1879_, v_i_1881_);
v_origin_1898_ = lean_ctor_get(v_a_1897_, 4);
if (lean_obj_tag(v_origin_1898_) == 0)
{
lean_object* v_priority_1899_; lean_object* v_declName_1900_; lean_object* v___x_1901_; 
v_priority_1899_ = lean_ctor_get(v_a_1897_, 3);
v_declName_1900_ = lean_ctor_get(v_origin_1898_, 0);
lean_inc(v_priority_1899_);
lean_inc(v_declName_1900_);
v___x_1901_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_declName_1900_, v_priority_1899_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
if (lean_obj_tag(v_a_1902_) == 1)
{
lean_object* v_val_1903_; lean_object* v_pattern_1904_; lean_object* v___x_1905_; 
v_val_1903_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v_a_1902_, 1);
v_pattern_1904_ = lean_ctor_get(v_val_1903_, 0);
lean_inc_ref(v_pattern_1904_);
v___x_1905_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_1882_, v_pattern_1904_, v_val_1903_);
v_a_1891_ = v___x_1905_;
goto v___jp_1890_;
}
else
{
lean_dec(v_a_1902_);
v_a_1891_ = v_b_1882_;
goto v___jp_1890_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1939_; 
v_a_1906_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1908_ = v___x_1901_;
v_isShared_1909_ = v_isSharedCheck_1939_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1901_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1939_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
uint8_t v___y_1911_; uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Exception_isInterrupt(v_a_1906_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
lean_inc(v_a_1906_);
v___x_1938_ = l_Lean_Exception_isRuntime(v_a_1906_);
v___y_1911_ = v___x_1938_;
goto v___jp_1910_;
}
else
{
v___y_1911_ = v___x_1937_;
goto v___jp_1910_;
}
v___jp_1910_:
{
if (v___y_1911_ == 0)
{
lean_object* v_options_1912_; uint8_t v_hasTrace_1913_; 
lean_del_object(v___x_1908_);
v_options_1912_ = lean_ctor_get(v___y_1887_, 2);
v_hasTrace_1913_ = lean_ctor_get_uint8(v_options_1912_, sizeof(void*)*1);
if (v_hasTrace_1913_ == 0)
{
lean_dec(v_a_1906_);
v_a_1891_ = v_b_1882_;
goto v___jp_1890_;
}
else
{
lean_object* v_inheritedTraceOptions_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_inheritedTraceOptions_1914_ = lean_ctor_get(v___y_1887_, 13);
v___x_1915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_1917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1914_, v_options_1912_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec(v_a_1906_);
v_a_1891_ = v_b_1882_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8);
lean_inc(v_declName_1900_);
v___x_1919_ = l_Lean_MessageData_ofName(v_declName_1900_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Lean_Exception_toMessageData(v_a_1906_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_1915_, v___x_1924_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_dec_ref_known(v___x_1925_, 1);
v_a_1891_ = v_b_1882_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_b_1882_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
else
{
lean_object* v___x_1935_; 
lean_dec_ref(v_b_1882_);
if (v_isShared_1909_ == 0)
{
v___x_1935_ = v___x_1908_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1906_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
else
{
v_a_1891_ = v_b_1882_;
goto v___jp_1890_;
}
}
v___jp_1890_:
{
size_t v___x_1892_; size_t v___x_1893_; 
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_add(v_i_1881_, v___x_1892_);
v_i_1881_ = v___x_1893_;
v_b_1882_ = v_a_1891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
size_t v_sz_boxed_1951_; size_t v_i_boxed_1952_; lean_object* v_res_1953_; 
v_sz_boxed_1951_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1952_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_as_1940_, v_sz_boxed_1951_, v_i_boxed_1952_, v_b_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_as_1940_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_a_1954_) == 0)
{
lean_object* v___x_1956_; 
v___x_1956_ = l_List_reverse___redArg(v_a_1955_);
return v___x_1956_;
}
else
{
lean_object* v_head_1957_; lean_object* v_tail_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1967_; 
v_head_1957_ = lean_ctor_get(v_a_1954_, 0);
v_tail_1958_ = lean_ctor_get(v_a_1954_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_a_1954_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1960_ = v_a_1954_;
v_isShared_1961_ = v_isSharedCheck_1967_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_tail_1958_);
lean_inc(v_head_1957_);
lean_dec(v_a_1954_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1967_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_fst_1962_; lean_object* v___x_1964_; 
v_fst_1962_ = lean_ctor_get(v_head_1957_, 0);
lean_inc(v_fst_1962_);
lean_dec(v_head_1957_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_a_1955_);
lean_ctor_set(v___x_1960_, 0, v_fst_1962_);
v___x_1964_ = v___x_1960_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_fst_1962_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_a_1955_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
v_a_1954_ = v_tail_1958_;
v_a_1955_ = v___x_1964_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0(lean_object* v_f_1968_, lean_object* v_x1_1969_, lean_object* v_x2_1970_, lean_object* v_x3_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_apply_3(v_f_1968_, v_x1_1969_, v_x2_1970_, v_x3_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(lean_object* v_f_1973_, lean_object* v_keys_1974_, lean_object* v_vals_1975_, lean_object* v_i_1976_, lean_object* v_acc_1977_){
_start:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = lean_array_get_size(v_keys_1974_);
v___x_1979_ = lean_nat_dec_lt(v_i_1976_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_dec(v_i_1976_);
lean_dec(v_f_1973_);
return v_acc_1977_;
}
else
{
lean_object* v_k_1980_; lean_object* v_v_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_k_1980_ = lean_array_fget_borrowed(v_keys_1974_, v_i_1976_);
v_v_1981_ = lean_array_fget_borrowed(v_vals_1975_, v_i_1976_);
lean_inc(v_f_1973_);
lean_inc(v_v_1981_);
lean_inc(v_k_1980_);
v___x_1982_ = lean_apply_3(v_f_1973_, v_acc_1977_, v_k_1980_, v_v_1981_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_add(v_i_1976_, v___x_1983_);
lean_dec(v_i_1976_);
v_i_1976_ = v___x_1984_;
v_acc_1977_ = v___x_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v_f_1986_, lean_object* v_keys_1987_, lean_object* v_vals_1988_, lean_object* v_i_1989_, lean_object* v_acc_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1986_, v_keys_1987_, v_vals_1988_, v_i_1989_, v_acc_1990_);
lean_dec_ref(v_vals_1988_);
lean_dec_ref(v_keys_1987_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(lean_object* v_f_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
if (lean_obj_tag(v_x_1993_) == 0)
{
lean_object* v_es_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_es_1995_ = lean_ctor_get(v_x_1993_, 0);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_array_get_size(v_es_1995_);
v___x_1998_ = lean_nat_dec_lt(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_dec(v_f_1992_);
return v_x_1994_;
}
else
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_nat_dec_le(v___x_1997_, v___x_1997_);
if (v___x_1999_ == 0)
{
if (v___x_1998_ == 0)
{
lean_dec(v_f_1992_);
return v_x_1994_;
}
else
{
size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = lean_usize_of_nat(v___x_1997_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1992_, v_es_1995_, v___x_2000_, v___x_2001_, v_x_1994_);
return v___x_2002_;
}
}
else
{
size_t v___x_2003_; size_t v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = lean_usize_of_nat(v___x_1997_);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_1992_, v_es_1995_, v___x_2003_, v___x_2004_, v_x_1994_);
return v___x_2005_;
}
}
}
else
{
lean_object* v_ks_2006_; lean_object* v_vs_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_ks_2006_ = lean_ctor_get(v_x_1993_, 0);
v_vs_2007_ = lean_ctor_get(v_x_1993_, 1);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1992_, v_ks_2006_, v_vs_2007_, v___x_2008_, v_x_1994_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(lean_object* v_f_2010_, lean_object* v_as_2011_, size_t v_i_2012_, size_t v_stop_2013_, lean_object* v_b_2014_){
_start:
{
lean_object* v___y_2016_; uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_eq(v_i_2012_, v_stop_2013_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_array_uget_borrowed(v_as_2011_, v_i_2012_);
switch(lean_obj_tag(v___x_2021_))
{
case 0:
{
lean_object* v_key_2022_; lean_object* v_val_2023_; lean_object* v___x_2024_; 
v_key_2022_ = lean_ctor_get(v___x_2021_, 0);
v_val_2023_ = lean_ctor_get(v___x_2021_, 1);
lean_inc(v_f_2010_);
lean_inc(v_val_2023_);
lean_inc(v_key_2022_);
v___x_2024_ = lean_apply_3(v_f_2010_, v_b_2014_, v_key_2022_, v_val_2023_);
v___y_2016_ = v___x_2024_;
goto v___jp_2015_;
}
case 1:
{
lean_object* v_node_2025_; lean_object* v___x_2026_; 
v_node_2025_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_f_2010_);
v___x_2026_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2010_, v_node_2025_, v_b_2014_);
v___y_2016_ = v___x_2026_;
goto v___jp_2015_;
}
default: 
{
v___y_2016_ = v_b_2014_;
goto v___jp_2015_;
}
}
}
else
{
lean_dec(v_f_2010_);
return v_b_2014_;
}
v___jp_2015_:
{
size_t v___x_2017_; size_t v___x_2018_; 
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2012_, v___x_2017_);
v_i_2012_ = v___x_2018_;
v_b_2014_ = v___y_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg___boxed(lean_object* v_f_2027_, lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_stop_2030_, lean_object* v_b_2031_){
_start:
{
size_t v_i_boxed_2032_; size_t v_stop_boxed_2033_; lean_object* v_res_2034_; 
v_i_boxed_2032_ = lean_unbox_usize(v_i_2029_);
lean_dec(v_i_2029_);
v_stop_boxed_2033_ = lean_unbox_usize(v_stop_2030_);
lean_dec(v_stop_2030_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_2027_, v_as_2028_, v_i_boxed_2032_, v_stop_boxed_2033_, v_b_2031_);
lean_dec_ref(v_as_2028_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(lean_object* v_f_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2035_, v_x_2036_, v_x_2037_);
lean_dec_ref(v_x_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(lean_object* v_map_2039_, lean_object* v_f_2040_, lean_object* v_init_2041_){
_start:
{
lean_object* v___f_2042_; lean_object* v___x_2043_; 
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2042_, 0, v_f_2040_);
v___x_2043_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2042_, v_map_2039_, v_init_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg___boxed(lean_object* v_map_2044_, lean_object* v_f_2045_, lean_object* v_init_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_map_2044_, v_f_2045_, v_init_2046_);
lean_dec_ref(v_map_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0(lean_object* v_ps_2048_, lean_object* v_k_2049_, lean_object* v_v_2050_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_k_2049_);
lean_ctor_set(v___x_2051_, 1, v_v_2050_);
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_ps_2048_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(lean_object* v_m_2054_){
_start:
{
lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___f_2055_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0));
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_m_2054_, v___f_2055_, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___boxed(lean_object* v_m_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_2058_);
lean_dec_ref(v_m_2058_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(lean_object* v_s_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_s_2060_);
v___x_2062_ = lean_box(0);
v___x_2063_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(v___x_2061_, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9___boxed(lean_object* v_s_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_s_2064_);
lean_dec_ref(v_s_2064_);
return v_res_2065_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0));
v___x_2068_ = l_Lean_stringToMessageData(v___x_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2));
v___x_2071_ = l_Lean_stringToMessageData(v___x_2070_);
return v___x_2071_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4));
v___x_2074_ = l_Lean_stringToMessageData(v___x_2073_);
return v___x_2074_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6));
v___x_2077_ = l_Lean_stringToMessageData(v___x_2076_);
return v___x_2077_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8));
v___x_2080_ = l_Lean_stringToMessageData(v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(lean_object* v_as_2081_, size_t v_sz_2082_, size_t v_i_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_a_2093_; uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2083_, v_sz_2082_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_b_2084_);
return v___x_2098_;
}
else
{
lean_object* v_a_2099_; lean_object* v_proof_2100_; lean_object* v_priority_2101_; lean_object* v___x_2102_; 
v_a_2099_ = lean_array_uget_borrowed(v_as_2081_, v_i_2083_);
v_proof_2100_ = lean_ctor_get(v_a_2099_, 2);
v_priority_2101_ = lean_ctor_get(v_a_2099_, 4);
lean_inc(v_priority_2101_);
lean_inc_ref(v_proof_2100_);
v___x_2102_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(v_proof_2100_, v_priority_2101_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
if (lean_obj_tag(v_a_2103_) == 1)
{
lean_object* v_val_2104_; lean_object* v_pattern_2105_; lean_object* v___x_2106_; 
v_val_2104_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_val_2104_);
lean_dec_ref_known(v_a_2103_, 1);
v_pattern_2105_ = lean_ctor_get(v_val_2104_, 0);
lean_inc_ref(v_pattern_2105_);
v___x_2106_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_2084_, v_pattern_2105_, v_val_2104_);
v_a_2093_ = v___x_2106_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2107_; lean_object* v___y_2109_; 
lean_dec(v_a_2103_);
v___x_2107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1);
switch(lean_obj_tag(v_proof_2100_))
{
case 0:
{
lean_object* v_declName_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_declName_2120_ = lean_ctor_get(v_proof_2100_, 0);
v___x_2121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3);
lean_inc(v_declName_2120_);
v___x_2122_ = l_Lean_MessageData_ofName(v_declName_2120_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___y_2109_ = v___x_2123_;
goto v___jp_2108_;
}
case 1:
{
lean_object* v_fvarId_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_fvarId_2124_ = lean_ctor_get(v_proof_2100_, 0);
v___x_2125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5);
lean_inc(v_fvarId_2124_);
v___x_2126_ = l_Lean_mkFVar(v_fvarId_2124_);
v___x_2127_ = l_Lean_MessageData_ofExpr(v___x_2126_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2125_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___y_2109_ = v___x_2128_;
goto v___jp_2108_;
}
default: 
{
lean_object* v_ref_2129_; lean_object* v_proof_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_ref_2129_ = lean_ctor_get(v_proof_2100_, 1);
v_proof_2130_ = lean_ctor_get(v_proof_2100_, 2);
v___x_2131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7);
lean_inc(v_ref_2129_);
v___x_2132_ = l_Lean_MessageData_ofSyntax(v_ref_2129_);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
lean_inc_ref(v_proof_2130_);
v___x_2136_ = l_Lean_MessageData_ofExpr(v_proof_2130_);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___y_2109_ = v___x_2137_;
goto v___jp_2108_;
}
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
lean_ctor_set(v___x_2110_, 1, v___y_2109_);
v___x_2111_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_2110_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_dec_ref_known(v___x_2111_, 1);
v_a_2093_ = v_b_2084_;
goto v___jp_2092_;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_b_2084_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_b_2084_);
v_a_2138_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2102_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2102_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
v___jp_2092_:
{
size_t v___x_2094_; size_t v___x_2095_; 
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_add(v_i_2083_, v___x_2094_);
v_i_2083_ = v___x_2095_;
v_b_2084_ = v_a_2093_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(lean_object* v_as_2146_, lean_object* v_sz_2147_, lean_object* v_i_2148_, lean_object* v_b_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
size_t v_sz_boxed_2157_; size_t v_i_boxed_2158_; lean_object* v_res_2159_; 
v_sz_boxed_2157_ = lean_unbox_usize(v_sz_2147_);
lean_dec(v_sz_2147_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_as_2146_, v_sz_boxed_2157_, v_i_boxed_2158_, v_b_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec_ref(v_as_2146_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(lean_object* v_keys_2160_, lean_object* v_vals_2161_, lean_object* v_i_2162_, lean_object* v_k_2163_){
_start:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_array_get_size(v_keys_2160_);
v___x_2165_ = lean_nat_dec_lt(v_i_2162_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_dec(v_i_2162_);
v___x_2166_ = lean_box(0);
return v___x_2166_;
}
else
{
lean_object* v_k_x27_2167_; uint8_t v___x_2168_; 
v_k_x27_2167_ = lean_array_fget_borrowed(v_keys_2160_, v_i_2162_);
v___x_2168_ = lean_name_eq(v_k_2163_, v_k_x27_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_add(v_i_2162_, v___x_2169_);
lean_dec(v_i_2162_);
v_i_2162_ = v___x_2170_;
goto _start;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_array_fget_borrowed(v_vals_2161_, v_i_2162_);
lean_dec(v_i_2162_);
lean_inc(v___x_2172_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg___boxed(lean_object* v_keys_2174_, lean_object* v_vals_2175_, lean_object* v_i_2176_, lean_object* v_k_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_keys_2174_, v_vals_2175_, v_i_2176_, v_k_2177_);
lean_dec(v_k_2177_);
lean_dec_ref(v_vals_2175_);
lean_dec_ref(v_keys_2174_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(lean_object* v_x_2179_, size_t v_x_2180_, lean_object* v_x_2181_){
_start:
{
if (lean_obj_tag(v_x_2179_) == 0)
{
lean_object* v_es_2182_; lean_object* v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v_j_2187_; lean_object* v___x_2188_; 
v_es_2182_ = lean_ctor_get(v_x_2179_, 0);
v___x_2183_ = lean_box(2);
v___x_2184_ = ((size_t)5ULL);
v___x_2185_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_2186_ = lean_usize_land(v_x_2180_, v___x_2185_);
v_j_2187_ = lean_usize_to_nat(v___x_2186_);
v___x_2188_ = lean_array_get_borrowed(v___x_2183_, v_es_2182_, v_j_2187_);
lean_dec(v_j_2187_);
switch(lean_obj_tag(v___x_2188_))
{
case 0:
{
lean_object* v_key_2189_; lean_object* v_val_2190_; uint8_t v___x_2191_; 
v_key_2189_ = lean_ctor_get(v___x_2188_, 0);
v_val_2190_ = lean_ctor_get(v___x_2188_, 1);
v___x_2191_ = lean_name_eq(v_x_2181_, v_key_2189_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_box(0);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; 
lean_inc(v_val_2190_);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_val_2190_);
return v___x_2193_;
}
}
case 1:
{
lean_object* v_node_2194_; size_t v___x_2195_; 
v_node_2194_ = lean_ctor_get(v___x_2188_, 0);
v___x_2195_ = lean_usize_shift_right(v_x_2180_, v___x_2184_);
v_x_2179_ = v_node_2194_;
v_x_2180_ = v___x_2195_;
goto _start;
}
default: 
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
}
}
else
{
lean_object* v_ks_2198_; lean_object* v_vs_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_ks_2198_ = lean_ctor_get(v_x_2179_, 0);
v_vs_2199_ = lean_ctor_get(v_x_2179_, 1);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_ks_2198_, v_vs_2199_, v___x_2200_, v_x_2181_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg___boxed(lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
size_t v_x_28209__boxed_2205_; lean_object* v_res_2206_; 
v_x_28209__boxed_2205_ = lean_unbox_usize(v_x_2203_);
lean_dec(v_x_2203_);
v_res_2206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2202_, v_x_28209__boxed_2205_, v_x_2204_);
lean_dec(v_x_2204_);
lean_dec_ref(v_x_2202_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(lean_object* v_x_2207_, lean_object* v_x_2208_){
_start:
{
uint64_t v___y_2210_; 
if (lean_obj_tag(v_x_2208_) == 0)
{
uint64_t v___x_2213_; 
v___x_2213_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2210_ = v___x_2213_;
goto v___jp_2209_;
}
else
{
uint64_t v_hash_2214_; 
v_hash_2214_ = lean_ctor_get_uint64(v_x_2208_, sizeof(void*)*2);
v___y_2210_ = v_hash_2214_;
goto v___jp_2209_;
}
v___jp_2209_:
{
size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_uint64_to_usize(v___y_2210_);
v___x_2212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2207_, v___x_2211_, v_x_2208_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg___boxed(lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2215_, v_x_2216_);
lean_dec(v_x_2216_);
lean_dec_ref(v_x_2215_);
return v_res_2217_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(lean_object* v_a_2224_, lean_object* v_as_2225_, size_t v_sz_2226_, size_t v_i_2227_, lean_object* v_b_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_snd_2237_; uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_lt(v_i_2227_, v_sz_2226_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_a_2224_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_b_2228_);
return v___x_2242_;
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_a_2243_ = lean_array_uget_borrowed(v_as_2225_, v_i_2227_);
v___x_2244_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_2243_);
v___x_2245_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_a_2243_, v___x_2244_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
if (lean_obj_tag(v_a_2246_) == 1)
{
lean_object* v_val_2247_; lean_object* v_pattern_2248_; lean_object* v___x_2249_; 
v_val_2247_ = lean_ctor_get(v_a_2246_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v_a_2246_, 1);
v_pattern_2248_ = lean_ctor_get(v_val_2247_, 0);
lean_inc_ref(v_pattern_2248_);
v___x_2249_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_2228_, v_pattern_2248_, v_val_2247_);
v_snd_2237_ = v___x_2249_;
goto v___jp_2236_;
}
else
{
lean_dec(v_a_2246_);
v_snd_2237_ = v_b_2228_;
goto v___jp_2236_;
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2287_; 
v_a_2250_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2252_ = v___x_2245_;
v_isShared_2253_ = v_isSharedCheck_2287_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2245_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2287_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
uint8_t v___y_2255_; uint8_t v___x_2285_; 
v___x_2285_ = l_Lean_Exception_isInterrupt(v_a_2250_);
if (v___x_2285_ == 0)
{
uint8_t v___x_2286_; 
lean_inc(v_a_2250_);
v___x_2286_ = l_Lean_Exception_isRuntime(v_a_2250_);
v___y_2255_ = v___x_2286_;
goto v___jp_2254_;
}
else
{
v___y_2255_ = v___x_2285_;
goto v___jp_2254_;
}
v___jp_2254_:
{
if (v___y_2255_ == 0)
{
lean_object* v_options_2256_; uint8_t v_hasTrace_2257_; 
lean_del_object(v___x_2252_);
v_options_2256_ = lean_ctor_get(v___y_2233_, 2);
v_hasTrace_2257_ = lean_ctor_get_uint8(v_options_2256_, sizeof(void*)*1);
if (v_hasTrace_2257_ == 0)
{
lean_dec(v_a_2250_);
v_snd_2237_ = v_b_2228_;
goto v___jp_2236_;
}
else
{
lean_object* v_inheritedTraceOptions_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_inheritedTraceOptions_2258_ = lean_ctor_get(v___y_2233_, 13);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_2260_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_2261_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2258_, v_options_2256_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_dec(v_a_2250_);
v_snd_2237_ = v_b_2228_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1);
lean_inc(v_a_2224_);
v___x_2263_ = l_Lean_MessageData_ofName(v_a_2224_);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
lean_inc(v_a_2243_);
v___x_2267_ = l_Lean_MessageData_ofName(v_a_2243_);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_Exception_toMessageData(v_a_2250_);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_2259_, v___x_2272_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_dec_ref_known(v___x_2273_, 1);
v_snd_2237_ = v_b_2228_;
goto v___jp_2236_;
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_b_2228_);
lean_dec(v_a_2224_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
else
{
lean_object* v___x_2283_; 
lean_dec_ref(v_b_2228_);
lean_dec(v_a_2224_);
if (v_isShared_2253_ == 0)
{
v___x_2283_ = v___x_2252_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2250_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
}
v___jp_2236_:
{
size_t v___x_2238_; size_t v___x_2239_; 
v___x_2238_ = ((size_t)1ULL);
v___x_2239_ = lean_usize_add(v_i_2227_, v___x_2238_);
v_i_2227_ = v___x_2239_;
v_b_2228_ = v_snd_2237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___boxed(lean_object* v_a_2288_, lean_object* v_as_2289_, lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_b_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
size_t v_sz_boxed_2300_; size_t v_i_boxed_2301_; lean_object* v_res_2302_; 
v_sz_boxed_2300_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2301_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_a_2288_, v_as_2289_, v_sz_boxed_2300_, v_i_boxed_2301_, v_b_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v_as_2289_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(lean_object* v_simpThms_2303_, lean_object* v_as_x27_2304_, lean_object* v_b_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
if (lean_obj_tag(v_as_x27_2304_) == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_b_2305_);
return v___x_2313_;
}
else
{
lean_object* v_head_2314_; lean_object* v_tail_2315_; lean_object* v_eqThms_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v_toUnfoldThms_2329_; lean_object* v___x_2330_; 
v_head_2314_ = lean_ctor_get(v_as_x27_2304_, 0);
v_tail_2315_ = lean_ctor_get(v_as_x27_2304_, 1);
v_toUnfoldThms_2329_ = lean_ctor_get(v_simpThms_2303_, 5);
v___x_2330_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_toUnfoldThms_2329_, v_head_2314_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v___x_2331_; 
lean_inc(v_head_2314_);
v___x_2331_ = l_Lean_Meta_getEqnsFor_x3f(v_head_2314_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
if (lean_obj_tag(v_a_2332_) == 1)
{
lean_object* v_val_2333_; 
v_val_2333_ = lean_ctor_get(v_a_2332_, 0);
lean_inc(v_val_2333_);
lean_dec_ref_known(v_a_2332_, 1);
v_eqThms_2317_ = v_val_2333_;
v___y_2318_ = v___y_2306_;
v___y_2319_ = v___y_2307_;
v___y_2320_ = v___y_2308_;
v___y_2321_ = v___y_2309_;
v___y_2322_ = v___y_2310_;
v___y_2323_ = v___y_2311_;
goto v___jp_2316_;
}
else
{
lean_dec(v_a_2332_);
v_as_x27_2304_ = v_tail_2315_;
goto _start;
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_b_2305_);
v_a_2335_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2331_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2331_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_val_2343_; 
v_val_2343_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_val_2343_);
lean_dec_ref_known(v___x_2330_, 1);
v_eqThms_2317_ = v_val_2343_;
v___y_2318_ = v___y_2306_;
v___y_2319_ = v___y_2307_;
v___y_2320_ = v___y_2308_;
v___y_2321_ = v___y_2309_;
v___y_2322_ = v___y_2310_;
v___y_2323_ = v___y_2311_;
goto v___jp_2316_;
}
v___jp_2316_:
{
size_t v_sz_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v_sz_2324_ = lean_array_size(v_eqThms_2317_);
v___x_2325_ = ((size_t)0ULL);
lean_inc(v_head_2314_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_head_2314_, v_eqThms_2317_, v_sz_2324_, v___x_2325_, v_b_2305_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec_ref(v_eqThms_2317_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_as_x27_2304_ = v_tail_2315_;
v_b_2305_ = v_a_2327_;
goto _start;
}
else
{
return v___x_2326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg___boxed(lean_object* v_simpThms_2344_, lean_object* v_as_x27_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2344_, v_as_x27_2345_, v_b_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v_as_x27_2345_);
lean_dec_ref(v_simpThms_2344_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(lean_object* v_database_2364_, lean_object* v_simpThms_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_specs_2373_; lean_object* v_erased_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2433_; 
v_specs_2373_ = lean_ctor_get(v_database_2364_, 0);
v_erased_2374_ = lean_ctor_get(v_database_2364_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_database_2364_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2376_ = v_database_2364_;
v_isShared_2377_ = v_isSharedCheck_2433_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_erased_2374_);
lean_inc(v_specs_2373_);
lean_dec(v_database_2364_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2433_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___f_2378_; lean_object* v_specs_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; size_t v_sz_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v___f_2378_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1));
v_specs_2379_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0);
v___x_2380_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2));
v___x_2381_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2378_, v_specs_2373_, v___x_2380_);
lean_dec_ref(v_specs_2373_);
v_sz_2382_ = lean_array_size(v___x_2381_);
v___x_2383_ = ((size_t)0ULL);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v___x_2381_, v_sz_2382_, v___x_2383_, v_specs_2379_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_2381_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v_post_2386_; lean_object* v_toUnfold_2387_; lean_object* v_erased_2388_; lean_object* v___f_2389_; lean_object* v___x_2390_; size_t v_sz_2391_; lean_object* v___x_2392_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v_post_2386_ = lean_ctor_get(v_simpThms_2365_, 1);
v_toUnfold_2387_ = lean_ctor_get(v_simpThms_2365_, 3);
v_erased_2388_ = lean_ctor_get(v_simpThms_2365_, 4);
v___f_2389_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4));
v___x_2390_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2389_, v_post_2386_, v___x_2380_);
v_sz_2391_ = lean_array_size(v___x_2390_);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v___x_2390_, v_sz_2391_, v___x_2383_, v_a_2385_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_2390_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_toUnfold_2387_);
v___x_2395_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2365_, v___x_2394_, v_a_2393_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2408_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___f_2400_; lean_object* v_erased_2401_; lean_object* v___x_2403_; 
v___f_2400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5));
v_erased_2401_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2400_, v_erased_2388_, v_erased_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v_erased_2401_);
lean_ctor_set(v___x_2376_, 0, v_a_2396_);
v___x_2403_ = v___x_2376_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2396_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_erased_2401_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2403_);
v___x_2405_ = v___x_2398_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_erased_2374_);
v_a_2409_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2395_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2395_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_erased_2374_);
v_a_2417_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2392_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2392_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_erased_2374_);
v_a_2425_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2384_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2384_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object* v_database_2434_, lean_object* v_simpThms_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(v_database_2434_, v_simpThms_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_simpThms_2435_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(lean_object* v_00_u03b2_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(v_x_2445_, v_x_2446_, v_x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(lean_object* v_cls_2449_, lean_object* v_msg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_2449_, v_msg_2450_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___boxed(lean_object* v_cls_2459_, lean_object* v_msg_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(v_cls_2459_, v_msg_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(lean_object* v_00_u03b2_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2470_, v_x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___boxed(lean_object* v_00_u03b2_2473_, lean_object* v_x_2474_, lean_object* v_x_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(v_00_u03b2_2473_, v_x_2474_, v_x_2475_);
lean_dec(v_x_2475_);
lean_dec_ref(v_x_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(lean_object* v_00_u03c3_2477_, lean_object* v_00_u03b1_2478_, lean_object* v_f_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_2479_, v_x_2480_, v_x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___boxed(lean_object* v_00_u03c3_2483_, lean_object* v_00_u03b1_2484_, lean_object* v_f_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(v_00_u03c3_2483_, v_00_u03b1_2484_, v_f_2485_, v_x_2486_, v_x_2487_);
lean_dec_ref(v_x_2487_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(lean_object* v_map_2489_, lean_object* v_f_2490_, lean_object* v_init_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2490_, v_map_2489_, v_init_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg___boxed(lean_object* v_map_2493_, lean_object* v_f_2494_, lean_object* v_init_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(v_map_2493_, v_f_2494_, v_init_2495_);
lean_dec_ref(v_map_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(lean_object* v_00_u03c3_2497_, lean_object* v_00_u03b2_2498_, lean_object* v_map_2499_, lean_object* v_f_2500_, lean_object* v_init_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2500_, v_map_2499_, v_init_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___boxed(lean_object* v_00_u03c3_2503_, lean_object* v_00_u03b2_2504_, lean_object* v_map_2505_, lean_object* v_f_2506_, lean_object* v_init_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(v_00_u03c3_2503_, v_00_u03b2_2504_, v_map_2505_, v_f_2506_, v_init_2507_);
lean_dec_ref(v_map_2505_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(lean_object* v_simpThms_2509_, lean_object* v_as_2510_, lean_object* v_as_x27_2511_, lean_object* v_b_2512_, lean_object* v_a_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2509_, v_as_x27_2511_, v_b_2512_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___boxed(lean_object* v_simpThms_2522_, lean_object* v_as_2523_, lean_object* v_as_x27_2524_, lean_object* v_b_2525_, lean_object* v_a_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(v_simpThms_2522_, v_as_2523_, v_as_x27_2524_, v_b_2525_, v_a_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v_as_x27_2524_);
lean_dec(v_as_2523_);
lean_dec_ref(v_simpThms_2522_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(lean_object* v_map_2535_, lean_object* v_f_2536_, lean_object* v_init_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2536_, v_map_2535_, v_init_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg___boxed(lean_object* v_map_2539_, lean_object* v_f_2540_, lean_object* v_init_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(v_map_2539_, v_f_2540_, v_init_2541_);
lean_dec_ref(v_map_2539_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(lean_object* v_00_u03c3_2543_, lean_object* v_00_u03b2_2544_, lean_object* v_map_2545_, lean_object* v_f_2546_, lean_object* v_init_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2546_, v_map_2545_, v_init_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___boxed(lean_object* v_00_u03c3_2549_, lean_object* v_00_u03b2_2550_, lean_object* v_map_2551_, lean_object* v_f_2552_, lean_object* v_init_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(v_00_u03c3_2549_, v_00_u03b2_2550_, v_map_2551_, v_f_2552_, v_init_2553_);
lean_dec_ref(v_map_2551_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(lean_object* v_00_u03b2_2555_, lean_object* v_x_2556_, size_t v_x_2557_, size_t v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_2556_, v_x_2557_, v_x_2558_, v_x_2559_, v_x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_){
_start:
{
size_t v_x_28720__boxed_2568_; size_t v_x_28721__boxed_2569_; lean_object* v_res_2570_; 
v_x_28720__boxed_2568_ = lean_unbox_usize(v_x_2564_);
lean_dec(v_x_2564_);
v_x_28721__boxed_2569_ = lean_unbox_usize(v_x_2565_);
lean_dec(v_x_2565_);
v_res_2570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(v_00_u03b2_2562_, v_x_2563_, v_x_28720__boxed_2568_, v_x_28721__boxed_2569_, v_x_2566_, v_x_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(lean_object* v_00_u03b2_2571_, lean_object* v_x_2572_, size_t v_x_2573_, lean_object* v_x_2574_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2572_, v_x_2573_, v_x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
size_t v_x_28737__boxed_2580_; lean_object* v_res_2581_; 
v_x_28737__boxed_2580_ = lean_unbox_usize(v_x_2578_);
lean_dec(v_x_2578_);
v_res_2581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(v_00_u03b2_2576_, v_x_2577_, v_x_28737__boxed_2580_, v_x_2579_);
lean_dec(v_x_2579_);
lean_dec_ref(v_x_2577_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03c3_2583_, lean_object* v_f_2584_, lean_object* v_as_2585_, size_t v_i_2586_, size_t v_stop_2587_, lean_object* v_b_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_2584_, v_as_2585_, v_i_2586_, v_stop_2587_, v_b_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03c3_2591_, lean_object* v_f_2592_, lean_object* v_as_2593_, lean_object* v_i_2594_, lean_object* v_stop_2595_, lean_object* v_b_2596_){
_start:
{
size_t v_i_boxed_2597_; size_t v_stop_boxed_2598_; lean_object* v_res_2599_; 
v_i_boxed_2597_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_stop_boxed_2598_ = lean_unbox_usize(v_stop_2595_);
lean_dec(v_stop_2595_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(v_00_u03b1_2590_, v_00_u03c3_2591_, v_f_2592_, v_as_2593_, v_i_boxed_2597_, v_stop_boxed_2598_, v_b_2596_);
lean_dec_ref(v_as_2593_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(lean_object* v_00_u03b1_2600_, lean_object* v_00_u03c3_2601_, lean_object* v_f_2602_, lean_object* v_as_2603_, size_t v_i_2604_, size_t v_stop_2605_, lean_object* v_b_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_2602_, v_as_2603_, v_i_2604_, v_stop_2605_, v_b_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_00_u03c3_2609_, lean_object* v_f_2610_, lean_object* v_as_2611_, lean_object* v_i_2612_, lean_object* v_stop_2613_, lean_object* v_b_2614_){
_start:
{
size_t v_i_boxed_2615_; size_t v_stop_boxed_2616_; lean_object* v_res_2617_; 
v_i_boxed_2615_ = lean_unbox_usize(v_i_2612_);
lean_dec(v_i_2612_);
v_stop_boxed_2616_ = lean_unbox_usize(v_stop_2613_);
lean_dec(v_stop_2613_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(v_00_u03b1_2608_, v_00_u03c3_2609_, v_f_2610_, v_as_2611_, v_i_boxed_2615_, v_stop_boxed_2616_, v_b_2614_);
lean_dec_ref(v_as_2611_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(lean_object* v_00_u03c3_2618_, lean_object* v_00_u03b1_2619_, lean_object* v_00_u03b2_2620_, lean_object* v_f_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2621_, v_x_2622_, v_x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___boxed(lean_object* v_00_u03c3_2625_, lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_f_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(v_00_u03c3_2625_, v_00_u03b1_2626_, v_00_u03b2_2627_, v_f_2628_, v_x_2629_, v_x_2630_);
lean_dec_ref(v_x_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(lean_object* v_00_u03b2_2632_, lean_object* v_m_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___boxed(lean_object* v_00_u03b2_2635_, lean_object* v_m_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(v_00_u03b2_2635_, v_m_2636_);
lean_dec_ref(v_m_2636_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2638_, lean_object* v_n_2639_, lean_object* v_k_2640_, lean_object* v_v_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_n_2639_, v_k_2640_, v_v_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2643_, size_t v_depth_2644_, lean_object* v_keys_2645_, lean_object* v_vals_2646_, lean_object* v_heq_2647_, lean_object* v_i_2648_, lean_object* v_entries_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_depth_2644_, v_keys_2645_, v_vals_2646_, v_i_2648_, v_entries_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2651_, lean_object* v_depth_2652_, lean_object* v_keys_2653_, lean_object* v_vals_2654_, lean_object* v_heq_2655_, lean_object* v_i_2656_, lean_object* v_entries_2657_){
_start:
{
size_t v_depth_boxed_2658_; lean_object* v_res_2659_; 
v_depth_boxed_2658_ = lean_unbox_usize(v_depth_2652_);
lean_dec(v_depth_2652_);
v_res_2659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(v_00_u03b2_2651_, v_depth_boxed_2658_, v_keys_2653_, v_vals_2654_, v_heq_2655_, v_i_2656_, v_entries_2657_);
lean_dec_ref(v_vals_2654_);
lean_dec_ref(v_keys_2653_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(lean_object* v_00_u03b2_2660_, lean_object* v_keys_2661_, lean_object* v_vals_2662_, lean_object* v_heq_2663_, lean_object* v_i_2664_, lean_object* v_k_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___redArg(v_keys_2661_, v_vals_2662_, v_i_2664_, v_k_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2667_, lean_object* v_keys_2668_, lean_object* v_vals_2669_, lean_object* v_heq_2670_, lean_object* v_i_2671_, lean_object* v_k_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__12(v_00_u03b2_2667_, v_keys_2668_, v_vals_2669_, v_heq_2670_, v_i_2671_, v_k_2672_);
lean_dec(v_k_2672_);
lean_dec_ref(v_vals_2669_);
lean_dec_ref(v_keys_2668_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(lean_object* v_00_u03b1_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_00_u03c3_2676_, lean_object* v_f_2677_, lean_object* v_as_2678_, size_t v_i_2679_, size_t v_stop_2680_, lean_object* v_b_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___redArg(v_f_2677_, v_as_2678_, v_i_2679_, v_stop_2680_, v_b_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_00_u03b2_2684_, lean_object* v_00_u03c3_2685_, lean_object* v_f_2686_, lean_object* v_as_2687_, lean_object* v_i_2688_, lean_object* v_stop_2689_, lean_object* v_b_2690_){
_start:
{
size_t v_i_boxed_2691_; size_t v_stop_boxed_2692_; lean_object* v_res_2693_; 
v_i_boxed_2691_ = lean_unbox_usize(v_i_2688_);
lean_dec(v_i_2688_);
v_stop_boxed_2692_ = lean_unbox_usize(v_stop_2689_);
lean_dec(v_stop_2689_);
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__18(v_00_u03b1_2683_, v_00_u03b2_2684_, v_00_u03c3_2685_, v_f_2686_, v_as_2687_, v_i_boxed_2691_, v_stop_boxed_2692_, v_b_2690_);
lean_dec_ref(v_as_2687_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object* v_00_u03c3_2694_, lean_object* v_00_u03b1_2695_, lean_object* v_00_u03b2_2696_, lean_object* v_f_2697_, lean_object* v_keys_2698_, lean_object* v_vals_2699_, lean_object* v_heq_2700_, lean_object* v_i_2701_, lean_object* v_acc_2702_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_2697_, v_keys_2698_, v_vals_2699_, v_i_2701_, v_acc_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object* v_00_u03c3_2704_, lean_object* v_00_u03b1_2705_, lean_object* v_00_u03b2_2706_, lean_object* v_f_2707_, lean_object* v_keys_2708_, lean_object* v_vals_2709_, lean_object* v_heq_2710_, lean_object* v_i_2711_, lean_object* v_acc_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(v_00_u03c3_2704_, v_00_u03b1_2705_, v_00_u03b2_2706_, v_f_2707_, v_keys_2708_, v_vals_2709_, v_heq_2710_, v_i_2711_, v_acc_2712_);
lean_dec_ref(v_vals_2709_);
lean_dec_ref(v_keys_2708_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(lean_object* v_00_u03c3_2714_, lean_object* v_00_u03b2_2715_, lean_object* v_map_2716_, lean_object* v_f_2717_, lean_object* v_init_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___redArg(v_map_2716_, v_f_2717_, v_init_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24___boxed(lean_object* v_00_u03c3_2720_, lean_object* v_00_u03b2_2721_, lean_object* v_map_2722_, lean_object* v_f_2723_, lean_object* v_init_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24(v_00_u03c3_2720_, v_00_u03b2_2721_, v_map_2722_, v_f_2723_, v_init_2724_);
lean_dec_ref(v_map_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13(lean_object* v_00_u03b2_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(v_x_2727_, v_x_2728_, v_x_2729_, v_x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21(lean_object* v_00_u03b2_2732_, lean_object* v_x_2733_, size_t v_x_2734_, size_t v_x_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___redArg(v_x_2733_, v_x_2734_, v_x_2735_, v_x_2736_, v_x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21___boxed(lean_object* v_00_u03b2_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
size_t v_x_28784__boxed_2745_; size_t v_x_28785__boxed_2746_; lean_object* v_res_2747_; 
v_x_28784__boxed_2745_ = lean_unbox_usize(v_x_2741_);
lean_dec(v_x_2741_);
v_x_28785__boxed_2746_ = lean_unbox_usize(v_x_2742_);
lean_dec(v_x_2742_);
v_res_2747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21(v_00_u03b2_2739_, v_x_2740_, v_x_28784__boxed_2745_, v_x_28785__boxed_2746_, v_x_2743_, v_x_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___redArg(lean_object* v_map_2748_, lean_object* v_f_2749_, lean_object* v_init_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2749_, v_map_2748_, v_init_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___redArg___boxed(lean_object* v_map_2752_, lean_object* v_f_2753_, lean_object* v_init_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___redArg(v_map_2752_, v_f_2753_, v_init_2754_);
lean_dec_ref(v_map_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32(lean_object* v_00_u03c3_2756_, lean_object* v_00_u03b2_2757_, lean_object* v_map_2758_, lean_object* v_f_2759_, lean_object* v_init_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2759_, v_map_2758_, v_init_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32___boxed(lean_object* v_00_u03c3_2762_, lean_object* v_00_u03b2_2763_, lean_object* v_map_2764_, lean_object* v_f_2765_, lean_object* v_init_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__24_spec__32(v_00_u03c3_2762_, v_00_u03b2_2763_, v_map_2764_, v_f_2765_, v_init_2766_);
lean_dec_ref(v_map_2764_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27(lean_object* v_x_2768_, lean_object* v_keys_2769_, lean_object* v_v_2770_, lean_object* v_k_2771_, lean_object* v_as_2772_, lean_object* v_k_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___redArg(v_x_2768_, v_keys_2769_, v_v_2770_, v_k_2771_, v_as_2772_, v_k_2773_, v_x_2774_, v_x_2775_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27___boxed(lean_object* v_x_2779_, lean_object* v_keys_2780_, lean_object* v_v_2781_, lean_object* v_k_2782_, lean_object* v_as_2783_, lean_object* v_k_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__18_spec__27(v_x_2779_, v_keys_2780_, v_v_2781_, v_k_2782_, v_as_2783_, v_k_2784_, v_x_2785_, v_x_2786_, v_x_2787_, v_x_2788_);
lean_dec_ref(v_k_2784_);
lean_dec_ref(v_keys_2780_);
lean_dec(v_x_2779_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32(lean_object* v_00_u03b2_2790_, lean_object* v_n_2791_, lean_object* v_k_2792_, lean_object* v_v_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32___redArg(v_n_2791_, v_k_2792_, v_v_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33(lean_object* v_00_u03b2_2795_, size_t v_depth_2796_, lean_object* v_keys_2797_, lean_object* v_vals_2798_, lean_object* v_heq_2799_, lean_object* v_i_2800_, lean_object* v_entries_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___redArg(v_depth_2796_, v_keys_2797_, v_vals_2798_, v_i_2800_, v_entries_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33___boxed(lean_object* v_00_u03b2_2803_, lean_object* v_depth_2804_, lean_object* v_keys_2805_, lean_object* v_vals_2806_, lean_object* v_heq_2807_, lean_object* v_i_2808_, lean_object* v_entries_2809_){
_start:
{
size_t v_depth_boxed_2810_; lean_object* v_res_2811_; 
v_depth_boxed_2810_ = lean_unbox_usize(v_depth_2804_);
lean_dec(v_depth_2804_);
v_res_2811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__33(v_00_u03b2_2803_, v_depth_boxed_2810_, v_keys_2805_, v_vals_2806_, v_heq_2807_, v_i_2808_, v_entries_2809_);
lean_dec_ref(v_vals_2806_);
lean_dec_ref(v_keys_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32_spec__37(lean_object* v_00_u03b2_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__21_spec__32_spec__37___redArg(v_x_2813_, v_x_2814_, v_x_2815_, v_x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(lean_object* v_xs_2818_, lean_object* v_j_2819_){
_start:
{
lean_object* v_zero_2820_; uint8_t v_isZero_2821_; 
v_zero_2820_ = lean_unsigned_to_nat(0u);
v_isZero_2821_ = lean_nat_dec_eq(v_j_2819_, v_zero_2820_);
if (v_isZero_2821_ == 1)
{
lean_dec(v_j_2819_);
return v_xs_2818_;
}
else
{
lean_object* v_one_2822_; lean_object* v_n_2823_; lean_object* v___x_2824_; lean_object* v_priority_2825_; lean_object* v___x_2826_; lean_object* v_priority_2827_; uint8_t v___x_2828_; 
v_one_2822_ = lean_unsigned_to_nat(1u);
v_n_2823_ = lean_nat_sub(v_j_2819_, v_one_2822_);
v___x_2824_ = lean_array_fget_borrowed(v_xs_2818_, v_n_2823_);
v_priority_2825_ = lean_ctor_get(v___x_2824_, 3);
v___x_2826_ = lean_array_fget_borrowed(v_xs_2818_, v_j_2819_);
v_priority_2827_ = lean_ctor_get(v___x_2826_, 3);
v___x_2828_ = lean_nat_dec_lt(v_priority_2825_, v_priority_2827_);
if (v___x_2828_ == 0)
{
lean_dec(v_n_2823_);
lean_dec(v_j_2819_);
return v_xs_2818_;
}
else
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_array_fswap(v_xs_2818_, v_j_2819_, v_n_2823_);
lean_dec(v_j_2819_);
v_xs_2818_ = v___x_2829_;
v_j_2819_ = v_n_2823_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(lean_object* v_xs_2831_, lean_object* v_i_2832_, lean_object* v_fuel_2833_){
_start:
{
lean_object* v_zero_2834_; uint8_t v_isZero_2835_; 
v_zero_2834_ = lean_unsigned_to_nat(0u);
v_isZero_2835_ = lean_nat_dec_eq(v_fuel_2833_, v_zero_2834_);
if (v_isZero_2835_ == 1)
{
lean_dec(v_fuel_2833_);
lean_dec(v_i_2832_);
return v_xs_2831_;
}
else
{
lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = lean_array_get_size(v_xs_2831_);
v___x_2837_ = lean_nat_dec_lt(v_i_2832_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_dec(v_fuel_2833_);
lean_dec(v_i_2832_);
return v_xs_2831_;
}
else
{
lean_object* v_one_2838_; lean_object* v_n_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_one_2838_ = lean_unsigned_to_nat(1u);
v_n_2839_ = lean_nat_sub(v_fuel_2833_, v_one_2838_);
lean_dec(v_fuel_2833_);
lean_inc(v_i_2832_);
v___x_2840_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(v_xs_2831_, v_i_2832_);
v___x_2841_ = lean_nat_add(v_i_2832_, v_one_2838_);
lean_dec(v_i_2832_);
v_xs_2831_ = v___x_2840_;
v_i_2832_ = v___x_2841_;
v_fuel_2833_ = v_n_2839_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2843_, lean_object* v_i_2844_, lean_object* v_k_2845_){
_start:
{
lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2846_ = lean_array_get_size(v_keys_2843_);
v___x_2847_ = lean_nat_dec_lt(v_i_2844_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_dec_ref(v_k_2845_);
lean_dec(v_i_2844_);
return v___x_2847_;
}
else
{
lean_object* v_k_x27_2848_; uint8_t v___x_2849_; 
v_k_x27_2848_ = lean_array_fget_borrowed(v_keys_2843_, v_i_2844_);
lean_inc(v_k_x27_2848_);
lean_inc_ref(v_k_2845_);
v___x_2849_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_k_2845_, v_k_x27_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_unsigned_to_nat(1u);
v___x_2851_ = lean_nat_add(v_i_2844_, v___x_2850_);
lean_dec(v_i_2844_);
v_i_2844_ = v___x_2851_;
goto _start;
}
else
{
lean_dec_ref(v_k_2845_);
lean_dec(v_i_2844_);
return v___x_2849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2853_, lean_object* v_i_2854_, lean_object* v_k_2855_){
_start:
{
uint8_t v_res_2856_; lean_object* v_r_2857_; 
v_res_2856_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_keys_2853_, v_i_2854_, v_k_2855_);
lean_dec_ref(v_keys_2853_);
v_r_2857_ = lean_box(v_res_2856_);
return v_r_2857_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(lean_object* v_x_2858_, size_t v_x_2859_, lean_object* v_x_2860_){
_start:
{
if (lean_obj_tag(v_x_2858_) == 0)
{
lean_object* v_es_2861_; lean_object* v___x_2862_; size_t v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; lean_object* v_j_2866_; lean_object* v___x_2867_; 
v_es_2861_ = lean_ctor_get(v_x_2858_, 0);
lean_inc_ref(v_es_2861_);
lean_dec_ref_known(v_x_2858_, 1);
v___x_2862_ = lean_box(2);
v___x_2863_ = ((size_t)5ULL);
v___x_2864_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_2865_ = lean_usize_land(v_x_2859_, v___x_2864_);
v_j_2866_ = lean_usize_to_nat(v___x_2865_);
v___x_2867_ = lean_array_get(v___x_2862_, v_es_2861_, v_j_2866_);
lean_dec(v_j_2866_);
lean_dec_ref(v_es_2861_);
switch(lean_obj_tag(v___x_2867_))
{
case 0:
{
lean_object* v_key_2868_; uint8_t v___x_2869_; 
v_key_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_key_2868_);
lean_dec_ref_known(v___x_2867_, 2);
v___x_2869_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_2860_, v_key_2868_);
return v___x_2869_;
}
case 1:
{
lean_object* v_node_2870_; size_t v___x_2871_; 
v_node_2870_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_node_2870_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2871_ = lean_usize_shift_right(v_x_2859_, v___x_2863_);
v_x_2858_ = v_node_2870_;
v_x_2859_ = v___x_2871_;
goto _start;
}
default: 
{
uint8_t v___x_2873_; 
lean_dec_ref(v_x_2860_);
v___x_2873_ = 0;
return v___x_2873_;
}
}
}
else
{
lean_object* v_ks_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v_ks_2874_ = lean_ctor_get(v_x_2858_, 0);
lean_inc_ref(v_ks_2874_);
lean_dec_ref_known(v_x_2858_, 2);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_ks_2874_, v___x_2875_, v_x_2860_);
lean_dec_ref(v_ks_2874_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg___boxed(lean_object* v_x_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_){
_start:
{
size_t v_x_4073__boxed_2880_; uint8_t v_res_2881_; lean_object* v_r_2882_; 
v_x_4073__boxed_2880_ = lean_unbox_usize(v_x_2878_);
lean_dec(v_x_2878_);
v_res_2881_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_2877_, v_x_4073__boxed_2880_, v_x_2879_);
v_r_2882_ = lean_box(v_res_2881_);
return v_r_2882_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
uint64_t v___y_2886_; lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_2884_);
if (lean_obj_tag(v___x_2889_) == 0)
{
uint64_t v___x_2890_; 
v___x_2890_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2886_ = v___x_2890_;
goto v___jp_2885_;
}
else
{
uint64_t v_hash_2891_; 
v_hash_2891_ = lean_ctor_get_uint64(v___x_2889_, sizeof(void*)*2);
lean_dec(v___x_2889_);
v___y_2886_ = v_hash_2891_;
goto v___jp_2885_;
}
v___jp_2885_:
{
size_t v___x_2887_; uint8_t v___x_2888_; 
v___x_2887_ = lean_uint64_to_usize(v___y_2886_);
v___x_2888_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_2883_, v___x_2887_, v_x_2884_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg___boxed(lean_object* v_x_2892_, lean_object* v_x_2893_){
_start:
{
uint8_t v_res_2894_; lean_object* v_r_2895_; 
v_res_2894_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_x_2892_, v_x_2893_);
v_r_2895_ = lean_box(v_res_2894_);
return v_r_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(lean_object* v_database_2896_, lean_object* v_as_2897_, size_t v_i_2898_, size_t v_stop_2899_, lean_object* v_b_2900_){
_start:
{
lean_object* v___y_2902_; uint8_t v___x_2906_; 
v___x_2906_ = lean_usize_dec_eq(v_i_2898_, v_stop_2899_);
if (v___x_2906_ == 0)
{
lean_object* v_erased_2907_; lean_object* v___x_2908_; lean_object* v_proof_2909_; uint8_t v___x_2910_; 
v_erased_2907_ = lean_ctor_get(v_database_2896_, 1);
v___x_2908_ = lean_array_uget_borrowed(v_as_2897_, v_i_2898_);
v_proof_2909_ = lean_ctor_get(v___x_2908_, 1);
lean_inc_ref(v_proof_2909_);
lean_inc_ref(v_erased_2907_);
v___x_2910_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_erased_2907_, v_proof_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_inc(v___x_2908_);
v___x_2911_ = lean_array_push(v_b_2900_, v___x_2908_);
v___y_2902_ = v___x_2911_;
goto v___jp_2901_;
}
else
{
v___y_2902_ = v_b_2900_;
goto v___jp_2901_;
}
}
else
{
lean_dec_ref(v_database_2896_);
return v_b_2900_;
}
v___jp_2901_:
{
size_t v___x_2903_; size_t v___x_2904_; 
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_i_2898_, v___x_2903_);
v_i_2898_ = v___x_2904_;
v_b_2900_ = v___y_2902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3___boxed(lean_object* v_database_2912_, lean_object* v_as_2913_, lean_object* v_i_2914_, lean_object* v_stop_2915_, lean_object* v_b_2916_){
_start:
{
size_t v_i_boxed_2917_; size_t v_stop_boxed_2918_; lean_object* v_res_2919_; 
v_i_boxed_2917_ = lean_unbox_usize(v_i_2914_);
lean_dec(v_i_2914_);
v_stop_boxed_2918_ = lean_unbox_usize(v_stop_2915_);
lean_dec(v_stop_2915_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_2912_, v_as_2913_, v_i_boxed_2917_, v_stop_boxed_2918_, v_b_2916_);
lean_dec_ref(v_as_2913_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(lean_object* v_a_2923_, lean_object* v_as_2924_, size_t v_sz_2925_, size_t v_i_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_usize_dec_lt(v_i_2926_, v_sz_2925_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref(v_a_2923_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_b_2927_);
return v___x_2936_;
}
else
{
lean_object* v_a_2937_; lean_object* v_pattern_2938_; lean_object* v___x_2939_; 
lean_dec_ref(v_b_2927_);
v_a_2937_ = lean_array_uget_borrowed(v_as_2924_, v_i_2926_);
v_pattern_2938_ = lean_ctor_get(v_a_2937_, 0);
lean_inc_ref(v_a_2923_);
lean_inc_ref(v_pattern_2938_);
v___x_2939_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_2938_, v_a_2923_, v___x_2935_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2962_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2962_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2962_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_box(0);
if (lean_obj_tag(v_a_2940_) == 1)
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_a_2923_);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v_a_2940_, 0);
lean_dec(v_unused_2957_);
v___x_2946_ = v_a_2940_;
v_isShared_2947_ = v_isSharedCheck_2956_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v_a_2940_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2956_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_inc(v_a_2937_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2937_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2944_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2951_);
v___x_2953_ = v___x_2942_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v___x_2958_; size_t v___x_2959_; size_t v___x_2960_; 
lean_del_object(v___x_2942_);
lean_dec(v_a_2940_);
v___x_2958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0));
v___x_2959_ = ((size_t)1ULL);
v___x_2960_ = lean_usize_add(v_i_2926_, v___x_2959_);
v_i_2926_ = v___x_2960_;
v_b_2927_ = v___x_2958_;
goto _start;
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_a_2923_);
v_a_2963_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2939_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2939_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___boxed(lean_object* v_a_2971_, lean_object* v_as_2972_, lean_object* v_sz_2973_, lean_object* v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
size_t v_sz_boxed_2983_; size_t v_i_boxed_2984_; lean_object* v_res_2985_; 
v_sz_boxed_2983_ = lean_unbox_usize(v_sz_2973_);
lean_dec(v_sz_2973_);
v_i_boxed_2984_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(v_a_2971_, v_as_2972_, v_sz_boxed_2983_, v_i_boxed_2984_, v_b_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_as_2972_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object* v_database_2986_, lean_object* v_e_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3068_; 
v___x_2995_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_2987_, v_a_2991_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3068_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3068_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2996_, v_a_2989_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3059_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3059_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3059_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v_specs_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___y_3009_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v_specs_3005_ = lean_ctor_get(v_database_2986_, 0);
v___x_3006_ = l_Lean_Meta_Sym_getMatch___redArg(v_specs_3005_, v_a_3001_);
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3049_ = lean_array_get_size(v___x_3006_);
v___x_3050_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___closed__0));
v___x_3051_ = lean_nat_dec_lt(v___x_3007_, v___x_3049_);
if (v___x_3051_ == 0)
{
lean_dec_ref(v___x_3006_);
lean_dec_ref(v_database_2986_);
v___y_3009_ = v___x_3050_;
goto v___jp_3008_;
}
else
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_nat_dec_le(v___x_3049_, v___x_3049_);
if (v___x_3052_ == 0)
{
if (v___x_3051_ == 0)
{
lean_dec_ref(v___x_3006_);
lean_dec_ref(v_database_2986_);
v___y_3009_ = v___x_3050_;
goto v___jp_3008_;
}
else
{
size_t v___x_3053_; size_t v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = ((size_t)0ULL);
v___x_3054_ = lean_usize_of_nat(v___x_3049_);
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_2986_, v___x_3006_, v___x_3053_, v___x_3054_, v___x_3050_);
lean_dec_ref(v___x_3006_);
v___y_3009_ = v___x_3055_;
goto v___jp_3008_;
}
}
else
{
size_t v___x_3056_; size_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = ((size_t)0ULL);
v___x_3057_ = lean_usize_of_nat(v___x_3049_);
v___x_3058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_2986_, v___x_3006_, v___x_3056_, v___x_3057_, v___x_3050_);
lean_dec_ref(v___x_3006_);
v___y_3009_ = v___x_3058_;
goto v___jp_3008_;
}
}
v___jp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = lean_array_get_size(v___y_3009_);
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_nat_dec_eq(v___x_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; size_t v_sz_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
lean_del_object(v___x_3003_);
v___x_3013_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v___y_3009_, v___x_3007_, v___x_3010_);
v___x_3014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0));
v_sz_3015_ = lean_array_size(v___x_3013_);
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(v_a_3001_, v___x_3013_, v_sz_3015_, v___x_3016_, v___x_3014_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3033_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3033_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3033_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v_fst_3022_; 
v_fst_3022_ = lean_ctor_get(v_a_3018_, 0);
lean_inc(v_fst_3022_);
lean_dec(v_a_3018_);
if (lean_obj_tag(v_fst_3022_) == 0)
{
lean_object* v___x_3024_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3013_);
v___x_3024_ = v___x_2998_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3013_);
v___x_3024_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3024_);
v___x_3026_ = v___x_3020_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
lean_object* v_val_3029_; lean_object* v___x_3031_; 
lean_dec_ref(v___x_3013_);
lean_del_object(v___x_2998_);
v_val_3029_ = lean_ctor_get(v_fst_3022_, 0);
lean_inc(v_val_3029_);
lean_dec_ref_known(v_fst_3022_, 1);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v_val_3029_);
v___x_3031_ = v___x_3020_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_val_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v___x_3013_);
lean_del_object(v___x_2998_);
v_a_3034_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3017_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3017_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
lean_dec(v_a_3001_);
v___x_3042_ = lean_array_fget(v___y_3009_, v___x_3007_);
lean_dec_ref(v___y_3009_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
lean_ctor_set(v___x_2998_, 0, v___x_3042_);
v___x_3044_ = v___x_2998_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3046_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3044_);
v___x_3046_ = v___x_3003_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_2998_);
lean_dec_ref(v_database_2986_);
v_a_3060_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3000_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3000_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(lean_object* v_database_3069_, lean_object* v_e_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(v_database_3069_, v_e_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
return v_res_3078_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(lean_object* v_00_u03b2_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_x_3080_, v_x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___boxed(lean_object* v_00_u03b2_3083_, lean_object* v_x_3084_, lean_object* v_x_3085_){
_start:
{
uint8_t v_res_3086_; lean_object* v_r_3087_; 
v_res_3086_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(v_00_u03b2_3083_, v_x_3084_, v_x_3085_);
v_r_3087_ = lean_box(v_res_3086_);
return v_r_3087_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(lean_object* v_00_u03b2_3088_, lean_object* v_x_3089_, size_t v_x_3090_, lean_object* v_x_3091_){
_start:
{
uint8_t v___x_3092_; 
v___x_3092_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_3089_, v_x_3090_, v_x_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_){
_start:
{
size_t v_x_4418__boxed_3097_; uint8_t v_res_3098_; lean_object* v_r_3099_; 
v_x_4418__boxed_3097_ = lean_unbox_usize(v_x_3095_);
lean_dec(v_x_3095_);
v_res_3098_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(v_00_u03b2_3093_, v_x_3094_, v_x_4418__boxed_3097_, v_x_3096_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2(lean_object* v_xs_3100_, lean_object* v_j_3101_, lean_object* v_h_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(v_xs_3100_, v_j_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3104_, lean_object* v_keys_3105_, lean_object* v_vals_3106_, lean_object* v_heq_3107_, lean_object* v_i_3108_, lean_object* v_k_3109_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_keys_3105_, v_i_3108_, v_k_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3111_, lean_object* v_keys_3112_, lean_object* v_vals_3113_, lean_object* v_heq_3114_, lean_object* v_i_3115_, lean_object* v_k_3116_){
_start:
{
uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_res_3117_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(v_00_u03b2_3111_, v_keys_3112_, v_vals_3113_, v_heq_3114_, v_i_3115_, v_k_3116_);
lean_dec_ref(v_vals_3113_);
lean_dec_ref(v_keys_3112_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
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
lean_object* initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
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
res = initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
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
