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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21_spec__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_26567__boxed_1232_; size_t v_x_26568__boxed_1233_; lean_object* v_res_1234_; 
v_x_26567__boxed_1232_ = lean_unbox_usize(v_x_1228_);
lean_dec(v_x_1228_);
v_x_26568__boxed_1233_ = lean_unbox_usize(v_x_1229_);
lean_dec(v_x_1229_);
v_res_1234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_1227_, v_x_26567__boxed_1232_, v_x_26568__boxed_1233_, v_x_1230_, v_x_1231_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v_ks_1257_; lean_object* v_vs_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1282_; 
v_ks_1257_ = lean_ctor_get(v_x_1253_, 0);
v_vs_1258_ = lean_ctor_get(v_x_1253_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1260_ = v_x_1253_;
v_isShared_1261_ = v_isSharedCheck_1282_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_vs_1258_);
lean_inc(v_ks_1257_);
lean_dec(v_x_1253_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1282_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = lean_array_get_size(v_ks_1257_);
v___x_1263_ = lean_nat_dec_lt(v_x_1254_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_dec(v_x_1254_);
v___x_1264_ = lean_array_push(v_ks_1257_, v_x_1255_);
v___x_1265_ = lean_array_push(v_vs_1258_, v_x_1256_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v___x_1265_);
lean_ctor_set(v___x_1260_, 0, v___x_1264_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
else
{
lean_object* v_k_x27_1269_; uint8_t v___x_1270_; 
v_k_x27_1269_ = lean_array_fget_borrowed(v_ks_1257_, v_x_1254_);
v___x_1270_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1255_, v_k_x27_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1272_; 
if (v_isShared_1261_ == 0)
{
v___x_1272_ = v___x_1260_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_ks_1257_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_vs_1258_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_add(v_x_1254_, v___x_1273_);
lean_dec(v_x_1254_);
v_x_1253_ = v___x_1272_;
v_x_1254_ = v___x_1274_;
goto _start;
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1277_ = lean_array_fset(v_ks_1257_, v_x_1254_, v_x_1255_);
v___x_1278_ = lean_array_fset(v_vs_1258_, v_x_1254_, v_x_1256_);
lean_dec(v_x_1254_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v___x_1278_);
lean_ctor_set(v___x_1260_, 0, v___x_1277_);
v___x_1280_ = v___x_1260_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(lean_object* v_n_1283_, lean_object* v_k_1284_, lean_object* v_v_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(v_n_1283_, v___x_1286_, v_k_1284_, v_v_1285_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(lean_object* v_x_1289_, size_t v_x_1290_, size_t v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
lean_object* v_es_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v_j_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_es_1294_ = lean_ctor_get(v_x_1289_, 0);
v___x_1295_ = ((size_t)5ULL);
v___x_1296_ = ((size_t)1ULL);
v___x_1297_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_1298_ = lean_usize_land(v_x_1290_, v___x_1297_);
v_j_1299_ = lean_usize_to_nat(v___x_1298_);
v___x_1300_ = lean_array_get_size(v_es_1294_);
v___x_1301_ = lean_nat_dec_lt(v_j_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v_j_1299_);
lean_dec(v_x_1293_);
lean_dec(v_x_1292_);
return v_x_1289_;
}
else
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1338_; 
lean_inc_ref(v_es_1294_);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_x_1289_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_x_1289_, 0);
lean_dec(v_unused_1339_);
v___x_1303_ = v_x_1289_;
v_isShared_1304_ = v_isSharedCheck_1338_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v_x_1289_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1338_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_v_1305_; lean_object* v___x_1306_; lean_object* v_xs_x27_1307_; lean_object* v___y_1309_; 
v_v_1305_ = lean_array_fget(v_es_1294_, v_j_1299_);
v___x_1306_ = lean_box(0);
v_xs_x27_1307_ = lean_array_fset(v_es_1294_, v_j_1299_, v___x_1306_);
switch(lean_obj_tag(v_v_1305_))
{
case 0:
{
lean_object* v_key_1314_; lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1325_; 
v_key_1314_ = lean_ctor_get(v_v_1305_, 0);
v_val_1315_ = lean_ctor_get(v_v_1305_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1317_ = v_v_1305_;
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_inc(v_key_1314_);
lean_dec(v_v_1305_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1292_, v_key_1314_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_del_object(v___x_1317_);
v___x_1320_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1314_, v_val_1315_, v_x_1292_, v_x_1293_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___y_1309_ = v___x_1321_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_val_1315_);
lean_dec(v_key_1314_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_x_1293_);
lean_ctor_set(v___x_1317_, 0, v_x_1292_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_x_1292_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_x_1293_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v___y_1309_ = v___x_1323_;
goto v___jp_1308_;
}
}
}
}
case 1:
{
lean_object* v_node_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1336_; 
v_node_1326_ = lean_ctor_get(v_v_1305_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1328_ = v_v_1305_;
v_isShared_1329_ = v_isSharedCheck_1336_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_node_1326_);
lean_dec(v_v_1305_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1336_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1330_ = lean_usize_shift_right(v_x_1290_, v___x_1295_);
v___x_1331_ = lean_usize_add(v_x_1291_, v___x_1296_);
v___x_1332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_node_1326_, v___x_1330_, v___x_1331_, v_x_1292_, v_x_1293_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1332_);
v___x_1334_ = v___x_1328_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
v___y_1309_ = v___x_1334_;
goto v___jp_1308_;
}
}
}
default: 
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_x_1292_);
lean_ctor_set(v___x_1337_, 1, v_x_1293_);
v___y_1309_ = v___x_1337_;
goto v___jp_1308_;
}
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_array_fset(v_xs_x27_1307_, v_j_1299_, v___y_1309_);
lean_dec(v_j_1299_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1310_);
v___x_1312_ = v___x_1303_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
else
{
lean_object* v_ks_1340_; lean_object* v_vs_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1361_; 
v_ks_1340_ = lean_ctor_get(v_x_1289_, 0);
v_vs_1341_ = lean_ctor_get(v_x_1289_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1289_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1343_ = v_x_1289_;
v_isShared_1344_ = v_isSharedCheck_1361_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_vs_1341_);
lean_inc(v_ks_1340_);
lean_dec(v_x_1289_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1361_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_ks_1340_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_vs_1341_);
v___x_1346_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v_newNode_1347_; uint8_t v___y_1349_; size_t v___x_1355_; uint8_t v___x_1356_; 
v_newNode_1347_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(v___x_1346_, v_x_1292_, v_x_1293_);
v___x_1355_ = ((size_t)7ULL);
v___x_1356_ = lean_usize_dec_le(v___x_1355_, v_x_1291_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1347_);
v___x_1358_ = lean_unsigned_to_nat(4u);
v___x_1359_ = lean_nat_dec_lt(v___x_1357_, v___x_1358_);
lean_dec(v___x_1357_);
v___y_1349_ = v___x_1359_;
goto v___jp_1348_;
}
else
{
v___y_1349_ = v___x_1356_;
goto v___jp_1348_;
}
v___jp_1348_:
{
if (v___y_1349_ == 0)
{
lean_object* v_ks_1350_; lean_object* v_vs_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_ks_1350_ = lean_ctor_get(v_newNode_1347_, 0);
lean_inc_ref(v_ks_1350_);
v_vs_1351_ = lean_ctor_get(v_newNode_1347_, 1);
lean_inc_ref(v_vs_1351_);
lean_dec_ref(v_newNode_1347_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0);
v___x_1354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(v_x_1291_, v_ks_1350_, v_vs_1351_, v___x_1352_, v___x_1353_);
lean_dec_ref(v_vs_1351_);
lean_dec_ref(v_ks_1350_);
return v___x_1354_;
}
else
{
return v_newNode_1347_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(size_t v_depth_1362_, lean_object* v_keys_1363_, lean_object* v_vals_1364_, lean_object* v_i_1365_, lean_object* v_entries_1366_){
_start:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_keys_1363_);
v___x_1368_ = lean_nat_dec_lt(v_i_1365_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_i_1365_);
return v_entries_1366_;
}
else
{
lean_object* v_k_1369_; lean_object* v_v_1370_; uint64_t v___x_1371_; size_t v_h_1372_; size_t v___x_1373_; lean_object* v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; size_t v_h_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_k_1369_ = lean_array_fget_borrowed(v_keys_1363_, v_i_1365_);
v_v_1370_ = lean_array_fget_borrowed(v_vals_1364_, v_i_1365_);
v___x_1371_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1369_);
v_h_1372_ = lean_uint64_to_usize(v___x_1371_);
v___x_1373_ = ((size_t)5ULL);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_sub(v_depth_1362_, v___x_1375_);
v___x_1377_ = lean_usize_mul(v___x_1373_, v___x_1376_);
v_h_1378_ = lean_usize_shift_right(v_h_1372_, v___x_1377_);
v___x_1379_ = lean_nat_add(v_i_1365_, v___x_1374_);
lean_dec(v_i_1365_);
lean_inc(v_v_1370_);
lean_inc(v_k_1369_);
v___x_1380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_entries_1366_, v_h_1378_, v_depth_1362_, v_k_1369_, v_v_1370_);
v_i_1365_ = v___x_1379_;
v_entries_1366_ = v___x_1380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg___boxed(lean_object* v_depth_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_i_1385_, lean_object* v_entries_1386_){
_start:
{
size_t v_depth_boxed_1387_; lean_object* v_res_1388_; 
v_depth_boxed_1387_ = lean_unbox_usize(v_depth_1382_);
lean_dec(v_depth_1382_);
v_res_1388_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(v_depth_boxed_1387_, v_keys_1383_, v_vals_1384_, v_i_1385_, v_entries_1386_);
lean_dec_ref(v_vals_1384_);
lean_dec_ref(v_keys_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___boxed(lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
size_t v_x_26849__boxed_1394_; size_t v_x_26850__boxed_1395_; lean_object* v_res_1396_; 
v_x_26849__boxed_1394_ = lean_unbox_usize(v_x_1390_);
lean_dec(v_x_1390_);
v_x_26850__boxed_1395_ = lean_unbox_usize(v_x_1391_);
lean_dec(v_x_1391_);
v_res_1396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_x_1389_, v_x_26849__boxed_1394_, v_x_26850__boxed_1395_, v_x_1392_, v_x_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
uint64_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1398_);
v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_x_1397_, v___x_1401_, v___x_1402_, v_x_1398_, v_x_1399_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(lean_object* v_keys_1404_, lean_object* v_vals_1405_, lean_object* v_i_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_array_get_size(v_keys_1404_);
v___x_1409_ = lean_nat_dec_lt(v_i_1406_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec(v_i_1406_);
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
else
{
lean_object* v_k_x27_1411_; uint8_t v___x_1412_; 
v_k_x27_1411_ = lean_array_fget_borrowed(v_keys_1404_, v_i_1406_);
v___x_1412_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1407_, v_k_x27_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_nat_add(v_i_1406_, v___x_1413_);
lean_dec(v_i_1406_);
v_i_1406_ = v___x_1414_;
goto _start;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_array_fget_borrowed(v_vals_1405_, v_i_1406_);
lean_dec(v_i_1406_);
lean_inc(v___x_1416_);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg___boxed(lean_object* v_keys_1418_, lean_object* v_vals_1419_, lean_object* v_i_1420_, lean_object* v_k_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(v_keys_1418_, v_vals_1419_, v_i_1420_, v_k_1421_);
lean_dec(v_k_1421_);
lean_dec_ref(v_vals_1419_);
lean_dec_ref(v_keys_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(lean_object* v_x_1423_, size_t v_x_1424_, lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_object* v_es_1426_; lean_object* v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v_j_1431_; lean_object* v___x_1432_; 
v_es_1426_ = lean_ctor_get(v_x_1423_, 0);
v___x_1427_ = lean_box(2);
v___x_1428_ = ((size_t)5ULL);
v___x_1429_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_1430_ = lean_usize_land(v_x_1424_, v___x_1429_);
v_j_1431_ = lean_usize_to_nat(v___x_1430_);
v___x_1432_ = lean_array_get_borrowed(v___x_1427_, v_es_1426_, v_j_1431_);
lean_dec(v_j_1431_);
switch(lean_obj_tag(v___x_1432_))
{
case 0:
{
lean_object* v_key_1433_; lean_object* v_val_1434_; uint8_t v___x_1435_; 
v_key_1433_ = lean_ctor_get(v___x_1432_, 0);
v_val_1434_ = lean_ctor_get(v___x_1432_, 1);
v___x_1435_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1425_, v_key_1433_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; 
lean_inc(v_val_1434_);
v___x_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_val_1434_);
return v___x_1437_;
}
}
case 1:
{
lean_object* v_node_1438_; size_t v___x_1439_; 
v_node_1438_ = lean_ctor_get(v___x_1432_, 0);
v___x_1439_ = lean_usize_shift_right(v_x_1424_, v___x_1428_);
v_x_1423_ = v_node_1438_;
v_x_1424_ = v___x_1439_;
goto _start;
}
default: 
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_box(0);
return v___x_1441_;
}
}
}
else
{
lean_object* v_ks_1442_; lean_object* v_vs_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_ks_1442_ = lean_ctor_get(v_x_1423_, 0);
v_vs_1443_ = lean_ctor_get(v_x_1423_, 1);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(v_ks_1442_, v_vs_1443_, v___x_1444_, v_x_1425_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg___boxed(lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
size_t v_x_27043__boxed_1449_; lean_object* v_res_1450_; 
v_x_27043__boxed_1449_ = lean_unbox_usize(v_x_1447_);
lean_dec(v_x_1447_);
v_res_1450_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(v_x_1446_, v_x_27043__boxed_1449_, v_x_1448_);
lean_dec(v_x_1448_);
lean_dec_ref(v_x_1446_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
uint64_t v___x_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1452_);
v___x_1454_ = lean_uint64_to_usize(v___x_1453_);
v___x_1455_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(v_x_1451_, v___x_1454_, v_x_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(v_x_1456_, v_x_1457_);
lean_dec(v_x_1457_);
lean_dec_ref(v_x_1456_);
return v_res_1458_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8(lean_object* v_msg_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0);
v___x_1462_ = lean_panic_fn_borrowed(v___x_1461_, v_msg_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21_spec__32(lean_object* v_vs_1463_, lean_object* v_v_1464_, lean_object* v_i_1465_){
_start:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_array_get_size(v_vs_1463_);
v___x_1467_ = lean_nat_dec_lt(v_i_1465_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec(v_i_1465_);
v___x_1468_ = lean_array_push(v_vs_1463_, v_v_1464_);
return v___x_1468_;
}
else
{
lean_object* v_proof_1469_; lean_object* v___x_1470_; lean_object* v_proof_1471_; uint8_t v___x_1472_; 
v_proof_1469_ = lean_ctor_get(v_v_1464_, 1);
v___x_1470_ = lean_array_fget_borrowed(v_vs_1463_, v_i_1465_);
v_proof_1471_ = lean_ctor_get(v___x_1470_, 1);
lean_inc_ref(v_proof_1471_);
lean_inc_ref(v_proof_1469_);
v___x_1472_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_1469_, v_proof_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_i_1465_, v___x_1473_);
lean_dec(v_i_1465_);
v_i_1465_ = v___x_1474_;
goto _start;
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_array_fset(v_vs_1463_, v_i_1465_, v_v_1464_);
lean_dec(v_i_1465_);
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21(lean_object* v_vs_1477_, lean_object* v_v_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21_spec__32(v_vs_1477_, v_v_1478_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(lean_object* v_x_1481_, lean_object* v_keys_1482_, lean_object* v_v_1483_, lean_object* v_k_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v_c_1488_; lean_object* v___x_1489_; 
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v_x_1481_, v___x_1486_);
v_c_1488_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1482_, v_v_1483_, v___x_1487_);
lean_dec(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_k_1484_);
lean_ctor_set(v___x_1489_, 1, v_c_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0___boxed(lean_object* v_x_1490_, lean_object* v_keys_1491_, lean_object* v_v_1492_, lean_object* v_k_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_1490_, v_keys_1491_, v_v_1492_, v_k_1493_, v_x_1494_);
lean_dec_ref(v_keys_1491_);
lean_dec(v_x_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(lean_object* v_a_1496_, lean_object* v_b_1497_){
_start:
{
lean_object* v_fst_1498_; lean_object* v_fst_1499_; uint8_t v___x_1500_; 
v_fst_1498_ = lean_ctor_get(v_a_1496_, 0);
v_fst_1499_ = lean_ctor_get(v_b_1497_, 0);
v___x_1500_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1498_, v_fst_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1___boxed(lean_object* v_a_1501_, lean_object* v_b_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_a_1501_, v_b_1502_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v_a_1501_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(lean_object* v_x_1509_, lean_object* v_keys_1510_, lean_object* v_v_1511_, lean_object* v_k_1512_, lean_object* v_as_1513_, lean_object* v_k_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_mid_1519_; lean_object* v_midVal_1520_; uint8_t v___x_1521_; 
v___x_1517_ = lean_nat_add(v_x_1515_, v_x_1516_);
v___x_1518_ = lean_unsigned_to_nat(1u);
v_mid_1519_ = lean_nat_shiftr(v___x_1517_, v___x_1518_);
lean_dec(v___x_1517_);
v_midVal_1520_ = lean_array_fget(v_as_1513_, v_mid_1519_);
v___x_1521_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_midVal_1520_, v_k_1514_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
lean_dec(v_x_1516_);
v___x_1522_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_k_1514_, v_midVal_1520_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
lean_dec(v_x_1515_);
v___x_1523_ = lean_array_get_size(v_as_1513_);
v___x_1524_ = lean_nat_dec_lt(v_mid_1519_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_dec(v_midVal_1520_);
lean_dec(v_mid_1519_);
lean_dec(v_k_1512_);
lean_dec_ref(v_v_1511_);
return v_as_1513_;
}
else
{
lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1537_; 
v_snd_1525_ = lean_ctor_get(v_midVal_1520_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_midVal_1520_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_midVal_1520_, 0);
lean_dec(v_unused_1538_);
v___x_1527_ = v_midVal_1520_;
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_dec(v_midVal_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1537_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_xs_x27_1530_; lean_object* v___x_1531_; lean_object* v_c_1532_; lean_object* v___x_1534_; 
v___x_1529_ = lean_box(0);
v_xs_x27_1530_ = lean_array_fset(v_as_1513_, v_mid_1519_, v___x_1529_);
v___x_1531_ = lean_nat_add(v_x_1509_, v___x_1518_);
v_c_1532_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_1510_, v_v_1511_, v___x_1531_, v_snd_1525_);
lean_dec(v___x_1531_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_c_1532_);
lean_ctor_set(v___x_1527_, 0, v_k_1512_);
v___x_1534_ = v___x_1527_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_c_1532_);
v___x_1534_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_array_fset(v_xs_x27_1530_, v_mid_1519_, v___x_1534_);
lean_dec(v_mid_1519_);
return v___x_1535_;
}
}
}
}
else
{
lean_dec(v_midVal_1520_);
v_x_1516_ = v_mid_1519_;
goto _start;
}
}
else
{
uint8_t v___x_1540_; 
lean_dec(v_midVal_1520_);
v___x_1540_ = lean_nat_dec_eq(v_mid_1519_, v_x_1515_);
if (v___x_1540_ == 0)
{
lean_dec(v_x_1515_);
v_x_1515_ = v_mid_1519_;
goto _start;
}
else
{
lean_object* v___x_1542_; lean_object* v_c_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_j_1546_; lean_object* v_as_1547_; lean_object* v___x_1548_; 
lean_dec(v_mid_1519_);
lean_dec(v_x_1516_);
v___x_1542_ = lean_nat_add(v_x_1509_, v___x_1518_);
v_c_1543_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1510_, v_v_1511_, v___x_1542_);
lean_dec(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_k_1512_);
lean_ctor_set(v___x_1544_, 1, v_c_1543_);
v___x_1545_ = lean_nat_add(v_x_1515_, v___x_1518_);
lean_dec(v_x_1515_);
v_j_1546_ = lean_array_get_size(v_as_1513_);
v_as_1547_ = lean_array_push(v_as_1513_, v___x_1544_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1545_, v_as_1547_, v_j_1546_);
lean_dec(v___x_1545_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(lean_object* v_x_1549_, lean_object* v_keys_1550_, lean_object* v_v_1551_, lean_object* v_k_1552_, lean_object* v_as_1553_, lean_object* v_k_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_array_get_size(v_as_1553_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_nat_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = lean_array_fget_borrowed(v_as_1553_, v___x_1556_);
v___x_1559_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_k_1554_, v___x_1558_);
if (v___x_1559_ == 0)
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v___x_1558_, v_k_1554_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_nat_dec_lt(v___x_1556_, v___x_1555_);
if (v___x_1561_ == 0)
{
lean_dec(v_k_1552_);
lean_dec_ref(v_v_1551_);
return v_as_1553_;
}
else
{
lean_object* v___x_1562_; lean_object* v_xs_x27_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_inc(v___x_1558_);
v___x_1562_ = lean_box(0);
v_xs_x27_1563_ = lean_array_fset(v_as_1553_, v___x_1556_, v___x_1562_);
v___x_1564_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(v_x_1549_, v_keys_1550_, v_v_1551_, v_k_1552_, v___x_1558_);
v___x_1565_ = lean_array_fset(v_xs_x27_1563_, v___x_1556_, v___x_1564_);
return v___x_1565_;
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_sub(v___x_1555_, v___x_1566_);
v___x_1568_ = lean_array_fget_borrowed(v_as_1553_, v___x_1567_);
v___x_1569_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v___x_1568_, v_k_1554_);
if (v___x_1569_ == 0)
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_k_1554_, v___x_1568_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_nat_dec_lt(v___x_1567_, v___x_1555_);
if (v___x_1571_ == 0)
{
lean_dec(v___x_1567_);
lean_dec(v_k_1552_);
lean_dec_ref(v_v_1551_);
return v_as_1553_;
}
else
{
lean_object* v___x_1572_; lean_object* v_xs_x27_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc(v___x_1568_);
v___x_1572_ = lean_box(0);
v_xs_x27_1573_ = lean_array_fset(v_as_1553_, v___x_1567_, v___x_1572_);
v___x_1574_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(v_x_1549_, v_keys_1550_, v_v_1551_, v_k_1552_, v___x_1568_);
v___x_1575_ = lean_array_fset(v_xs_x27_1573_, v___x_1567_, v___x_1574_);
lean_dec(v___x_1567_);
return v___x_1575_;
}
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(v_x_1549_, v_keys_1550_, v_v_1551_, v_k_1552_, v_as_1553_, v_k_1554_, v___x_1556_, v___x_1567_);
return v___x_1576_;
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v___x_1567_);
v___x_1577_ = lean_box(0);
v___x_1578_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_1549_, v_keys_1550_, v_v_1551_, v_k_1552_, v___x_1577_);
v___x_1579_ = lean_array_push(v_as_1553_, v___x_1578_);
return v___x_1579_;
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_as_1582_; lean_object* v___x_1583_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_1549_, v_keys_1550_, v_v_1551_, v_k_1552_, v___x_1580_);
v_as_1582_ = lean_array_push(v_as_1553_, v___x_1581_);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_1556_, v_as_1582_, v___x_1555_);
return v___x_1583_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_1549_, v_keys_1550_, v_v_1551_, v_k_1552_, v___x_1584_);
v___x_1586_ = lean_array_push(v_as_1553_, v___x_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(lean_object* v_keys_1587_, lean_object* v_v_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v_vs_1591_; lean_object* v_children_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1609_; 
v_vs_1591_ = lean_ctor_get(v_x_1590_, 0);
v_children_1592_ = lean_ctor_get(v_x_1590_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1590_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1594_ = v_x_1590_;
v_isShared_1595_ = v_isSharedCheck_1609_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_children_1592_);
lean_inc(v_vs_1591_);
lean_dec(v_x_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1609_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_array_get_size(v_keys_1587_);
v___x_1597_ = lean_nat_dec_lt(v_x_1589_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21(v_vs_1591_, v_v_1588_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1598_);
v___x_1600_ = v___x_1594_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_children_1592_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
else
{
lean_object* v_k_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_c_1605_; lean_object* v___x_1607_; 
v_k_1602_ = lean_array_fget_borrowed(v_keys_1587_, v_x_1589_);
v___x_1603_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1));
lean_inc_n(v_k_1602_, 2);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v_k_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v_c_1605_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(v_x_1589_, v_keys_1587_, v_v_1588_, v_k_1602_, v_children_1592_, v___x_1604_);
lean_dec_ref_known(v___x_1604_, 2);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v_c_1605_);
v___x_1607_ = v___x_1594_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_vs_1591_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_c_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(lean_object* v_x_1610_, lean_object* v_keys_1611_, lean_object* v_v_1612_, lean_object* v_k_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_snd_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1625_; 
v_snd_1615_ = lean_ctor_get(v_x_1614_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1614_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v_x_1614_, 0);
lean_dec(v_unused_1626_);
v___x_1617_ = v_x_1614_;
v_isShared_1618_ = v_isSharedCheck_1625_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_snd_1615_);
lean_dec(v_x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1625_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_c_1621_; lean_object* v___x_1623_; 
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v_x_1610_, v___x_1619_);
v_c_1621_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_1611_, v_v_1612_, v___x_1620_, v_snd_1615_);
lean_dec(v___x_1620_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v_c_1621_);
lean_ctor_set(v___x_1617_, 0, v_k_1613_);
v___x_1623_ = v___x_1617_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_k_1613_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_c_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2___boxed(lean_object* v_x_1627_, lean_object* v_keys_1628_, lean_object* v_v_1629_, lean_object* v_k_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(v_x_1627_, v_keys_1628_, v_v_1629_, v_k_1630_, v_x_1631_);
lean_dec_ref(v_keys_1628_);
lean_dec(v_x_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___boxed(lean_object* v_keys_1633_, lean_object* v_v_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_1633_, v_v_1634_, v_x_1635_, v_x_1636_);
lean_dec(v_x_1635_);
lean_dec_ref(v_keys_1633_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg___boxed(lean_object* v_x_1638_, lean_object* v_keys_1639_, lean_object* v_v_1640_, lean_object* v_k_1641_, lean_object* v_as_1642_, lean_object* v_k_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(v_x_1638_, v_keys_1639_, v_v_1640_, v_k_1641_, v_as_1642_, v_k_1643_, v_x_1644_, v_x_1645_);
lean_dec_ref(v_k_1643_);
lean_dec_ref(v_keys_1639_);
lean_dec(v_x_1638_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___boxed(lean_object* v_x_1647_, lean_object* v_keys_1648_, lean_object* v_v_1649_, lean_object* v_k_1650_, lean_object* v_as_1651_, lean_object* v_k_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(v_x_1647_, v_keys_1648_, v_v_1649_, v_k_1650_, v_as_1651_, v_k_1652_);
lean_dec_ref(v_k_1652_);
lean_dec_ref(v_keys_1648_);
lean_dec(v_x_1647_);
return v_res_1653_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2));
v___x_1658_ = lean_unsigned_to_nat(23u);
v___x_1659_ = lean_unsigned_to_nat(166u);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1));
v___x_1661_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0));
v___x_1662_ = l_mkPanicMessageWithDecl(v___x_1661_, v___x_1660_, v___x_1659_, v___x_1658_, v___x_1657_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(lean_object* v_d_1663_, lean_object* v_keys_1664_, lean_object* v_v_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = lean_array_get_size(v_keys_1664_);
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = lean_nat_dec_eq(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v_k_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v_k_1670_ = lean_array_get_borrowed(v___x_1669_, v_keys_1664_, v___x_1667_);
v___x_1671_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(v_d_1663_, v_k_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1672_; lean_object* v_c_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_unsigned_to_nat(1u);
v_c_1673_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1664_, v_v_1665_, v___x_1672_);
lean_inc(v_k_1670_);
v___x_1674_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(v_d_1663_, v_k_1670_, v_c_1673_);
return v___x_1674_;
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1676_; lean_object* v_c_1677_; lean_object* v___x_1678_; 
v_val_1675_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1676_ = lean_unsigned_to_nat(1u);
v_c_1677_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_1664_, v_v_1665_, v___x_1676_, v_val_1675_);
lean_inc(v_k_1670_);
v___x_1678_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(v_d_1663_, v_k_1670_, v_c_1677_);
return v___x_1678_;
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v_v_1665_);
lean_dec_ref(v_d_1663_);
v___x_1679_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3);
v___x_1680_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8(v___x_1679_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(lean_object* v_d_1681_, lean_object* v_keys_1682_, lean_object* v_v_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_d_1681_, v_keys_1682_, v_v_1683_);
lean_dec_ref(v_keys_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(lean_object* v_d_1685_, lean_object* v_p_1686_, lean_object* v_v_1687_){
_start:
{
lean_object* v_keys_1688_; lean_object* v___x_1689_; 
v_keys_1688_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_1686_);
v___x_1689_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_d_1685_, v_keys_1688_, v_v_1687_);
lean_dec_ref(v_keys_1688_);
return v___x_1689_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1690_; double v___x_1691_; 
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_float_of_nat(v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(lean_object* v_cls_1695_, lean_object* v_msg_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_ref_1702_; lean_object* v___x_1703_; lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1748_; 
v_ref_1702_ = lean_ctor_get(v___y_1699_, 5);
v___x_1703_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1748_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1748_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v_traceState_1709_; lean_object* v_env_1710_; lean_object* v_nextMacroScope_1711_; lean_object* v_ngen_1712_; lean_object* v_auxDeclNGen_1713_; lean_object* v_cache_1714_; lean_object* v_messages_1715_; lean_object* v_infoState_1716_; lean_object* v_snapshotTasks_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1747_; 
v___x_1708_ = lean_st_ref_take(v___y_1700_);
v_traceState_1709_ = lean_ctor_get(v___x_1708_, 4);
v_env_1710_ = lean_ctor_get(v___x_1708_, 0);
v_nextMacroScope_1711_ = lean_ctor_get(v___x_1708_, 1);
v_ngen_1712_ = lean_ctor_get(v___x_1708_, 2);
v_auxDeclNGen_1713_ = lean_ctor_get(v___x_1708_, 3);
v_cache_1714_ = lean_ctor_get(v___x_1708_, 5);
v_messages_1715_ = lean_ctor_get(v___x_1708_, 6);
v_infoState_1716_ = lean_ctor_get(v___x_1708_, 7);
v_snapshotTasks_1717_ = lean_ctor_get(v___x_1708_, 8);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1719_ = v___x_1708_;
v_isShared_1720_ = v_isSharedCheck_1747_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snapshotTasks_1717_);
lean_inc(v_infoState_1716_);
lean_inc(v_messages_1715_);
lean_inc(v_cache_1714_);
lean_inc(v_traceState_1709_);
lean_inc(v_auxDeclNGen_1713_);
lean_inc(v_ngen_1712_);
lean_inc(v_nextMacroScope_1711_);
lean_inc(v_env_1710_);
lean_dec(v___x_1708_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1747_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
uint64_t v_tid_1721_; lean_object* v_traces_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1746_; 
v_tid_1721_ = lean_ctor_get_uint64(v_traceState_1709_, sizeof(void*)*1);
v_traces_1722_ = lean_ctor_get(v_traceState_1709_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_traceState_1709_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1724_ = v_traceState_1709_;
v_isShared_1725_ = v_isSharedCheck_1746_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_traces_1722_);
lean_dec(v_traceState_1709_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1746_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; double v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0);
v___x_1728_ = 0;
v___x_1729_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1));
v___x_1730_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1730_, 0, v_cls_1695_);
lean_ctor_set(v___x_1730_, 1, v___x_1726_);
lean_ctor_set(v___x_1730_, 2, v___x_1729_);
lean_ctor_set_float(v___x_1730_, sizeof(void*)*3, v___x_1727_);
lean_ctor_set_float(v___x_1730_, sizeof(void*)*3 + 8, v___x_1727_);
lean_ctor_set_uint8(v___x_1730_, sizeof(void*)*3 + 16, v___x_1728_);
v___x_1731_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2));
v___x_1732_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v_a_1704_);
lean_ctor_set(v___x_1732_, 2, v___x_1731_);
lean_inc(v_ref_1702_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_ref_1702_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_PersistentArray_push___redArg(v_traces_1722_, v___x_1733_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1734_);
v___x_1736_ = v___x_1724_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1734_);
lean_ctor_set_uint64(v_reuseFailAlloc_1745_, sizeof(void*)*1, v_tid_1721_);
v___x_1736_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v___x_1736_);
v___x_1738_ = v___x_1719_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_env_1710_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_nextMacroScope_1711_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_ngen_1712_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_auxDeclNGen_1713_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1744_, 5, v_cache_1714_);
lean_ctor_set(v_reuseFailAlloc_1744_, 6, v_messages_1715_);
lean_ctor_set(v_reuseFailAlloc_1744_, 7, v_infoState_1716_);
lean_ctor_set(v_reuseFailAlloc_1744_, 8, v_snapshotTasks_1717_);
v___x_1738_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1739_ = lean_st_ref_set(v___y_1700_, v___x_1738_);
v___x_1740_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1740_);
v___x_1742_ = v___x_1706_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___boxed(lean_object* v_cls_1749_, lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_1749_, v_msg_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1756_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5));
v___x_1770_ = l_Lean_Name_append(v___x_1769_, v___x_1768_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(lean_object* v_as_1777_, size_t v_sz_1778_, size_t v_i_1779_, lean_object* v_b_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_a_1789_; uint8_t v___x_1793_; 
v___x_1793_ = lean_usize_dec_lt(v_i_1779_, v_sz_1778_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_b_1780_);
return v___x_1794_;
}
else
{
lean_object* v_a_1795_; lean_object* v_origin_1796_; 
v_a_1795_ = lean_array_uget_borrowed(v_as_1777_, v_i_1779_);
v_origin_1796_ = lean_ctor_get(v_a_1795_, 4);
if (lean_obj_tag(v_origin_1796_) == 0)
{
lean_object* v_priority_1797_; lean_object* v_declName_1798_; lean_object* v___x_1799_; 
v_priority_1797_ = lean_ctor_get(v_a_1795_, 3);
v_declName_1798_ = lean_ctor_get(v_origin_1796_, 0);
lean_inc(v_priority_1797_);
lean_inc(v_declName_1798_);
v___x_1799_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_declName_1798_, v_priority_1797_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
if (lean_obj_tag(v_a_1800_) == 1)
{
lean_object* v_val_1801_; lean_object* v_pattern_1802_; lean_object* v___x_1803_; 
v_val_1801_ = lean_ctor_get(v_a_1800_, 0);
lean_inc(v_val_1801_);
lean_dec_ref_known(v_a_1800_, 1);
v_pattern_1802_ = lean_ctor_get(v_val_1801_, 0);
lean_inc_ref(v_pattern_1802_);
v___x_1803_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_1780_, v_pattern_1802_, v_val_1801_);
v_a_1789_ = v___x_1803_;
goto v___jp_1788_;
}
else
{
lean_dec(v_a_1800_);
v_a_1789_ = v_b_1780_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1837_; 
v_a_1804_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1806_ = v___x_1799_;
v_isShared_1807_ = v_isSharedCheck_1837_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1799_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1837_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
uint8_t v___y_1809_; uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Exception_isInterrupt(v_a_1804_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; 
lean_inc(v_a_1804_);
v___x_1836_ = l_Lean_Exception_isRuntime(v_a_1804_);
v___y_1809_ = v___x_1836_;
goto v___jp_1808_;
}
else
{
v___y_1809_ = v___x_1835_;
goto v___jp_1808_;
}
v___jp_1808_:
{
if (v___y_1809_ == 0)
{
lean_object* v_options_1810_; uint8_t v_hasTrace_1811_; 
lean_del_object(v___x_1806_);
v_options_1810_ = lean_ctor_get(v___y_1785_, 2);
v_hasTrace_1811_ = lean_ctor_get_uint8(v_options_1810_, sizeof(void*)*1);
if (v_hasTrace_1811_ == 0)
{
lean_dec(v_a_1804_);
v_a_1789_ = v_b_1780_;
goto v___jp_1788_;
}
else
{
lean_object* v_inheritedTraceOptions_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v_inheritedTraceOptions_1812_ = lean_ctor_get(v___y_1785_, 13);
v___x_1813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_1814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_1815_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1812_, v_options_1810_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_dec(v_a_1804_);
v_a_1789_ = v_b_1780_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8);
lean_inc(v_declName_1798_);
v___x_1817_ = l_Lean_MessageData_ofName(v_declName_1798_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_Exception_toMessageData(v_a_1804_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_1813_, v___x_1822_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_dec_ref_known(v___x_1823_, 1);
v_a_1789_ = v_b_1780_;
goto v___jp_1788_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v_b_1780_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref(v_b_1780_);
if (v_isShared_1807_ == 0)
{
v___x_1833_ = v___x_1806_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1804_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
else
{
v_a_1789_ = v_b_1780_;
goto v___jp_1788_;
}
}
v___jp_1788_:
{
size_t v___x_1790_; size_t v___x_1791_; 
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_add(v_i_1779_, v___x_1790_);
v_i_1779_ = v___x_1791_;
v_b_1780_ = v_a_1789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(lean_object* v_as_1838_, lean_object* v_sz_1839_, lean_object* v_i_1840_, lean_object* v_b_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
size_t v_sz_boxed_1849_; size_t v_i_boxed_1850_; lean_object* v_res_1851_; 
v_sz_boxed_1849_ = lean_unbox_usize(v_sz_1839_);
lean_dec(v_sz_1839_);
v_i_boxed_1850_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_as_1838_, v_sz_boxed_1849_, v_i_boxed_1850_, v_b_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec_ref(v_as_1838_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
if (lean_obj_tag(v_a_1852_) == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = l_List_reverse___redArg(v_a_1853_);
return v___x_1854_;
}
else
{
lean_object* v_head_1855_; lean_object* v_tail_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1865_; 
v_head_1855_ = lean_ctor_get(v_a_1852_, 0);
v_tail_1856_ = lean_ctor_get(v_a_1852_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_a_1852_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1858_ = v_a_1852_;
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_tail_1856_);
lean_inc(v_head_1855_);
lean_dec(v_a_1852_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_fst_1860_; lean_object* v___x_1862_; 
v_fst_1860_ = lean_ctor_get(v_head_1855_, 0);
lean_inc(v_fst_1860_);
lean_dec(v_head_1855_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_a_1853_);
lean_ctor_set(v___x_1858_, 0, v_fst_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_fst_1860_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_a_1853_);
v___x_1862_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
v_a_1852_ = v_tail_1856_;
v_a_1853_ = v___x_1862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(lean_object* v_f_1866_, lean_object* v_keys_1867_, lean_object* v_vals_1868_, lean_object* v_i_1869_, lean_object* v_acc_1870_){
_start:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = lean_array_get_size(v_keys_1867_);
v___x_1872_ = lean_nat_dec_lt(v_i_1869_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_dec(v_i_1869_);
lean_dec(v_f_1866_);
return v_acc_1870_;
}
else
{
lean_object* v_k_1873_; lean_object* v_v_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_k_1873_ = lean_array_fget_borrowed(v_keys_1867_, v_i_1869_);
v_v_1874_ = lean_array_fget_borrowed(v_vals_1868_, v_i_1869_);
lean_inc(v_f_1866_);
lean_inc(v_v_1874_);
lean_inc(v_k_1873_);
v___x_1875_ = lean_apply_3(v_f_1866_, v_acc_1870_, v_k_1873_, v_v_1874_);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_add(v_i_1869_, v___x_1876_);
lean_dec(v_i_1869_);
v_i_1869_ = v___x_1877_;
v_acc_1870_ = v___x_1875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg___boxed(lean_object* v_f_1879_, lean_object* v_keys_1880_, lean_object* v_vals_1881_, lean_object* v_i_1882_, lean_object* v_acc_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(v_f_1879_, v_keys_1880_, v_vals_1881_, v_i_1882_, v_acc_1883_);
lean_dec_ref(v_vals_1881_);
lean_dec_ref(v_keys_1880_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(lean_object* v_f_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v_es_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_es_1888_ = lean_ctor_get(v_x_1886_, 0);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_array_get_size(v_es_1888_);
v___x_1891_ = lean_nat_dec_lt(v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_dec(v_f_1885_);
return v_x_1887_;
}
else
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_nat_dec_le(v___x_1890_, v___x_1890_);
if (v___x_1892_ == 0)
{
if (v___x_1891_ == 0)
{
lean_dec(v_f_1885_);
return v_x_1887_;
}
else
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((size_t)0ULL);
v___x_1894_ = lean_usize_of_nat(v___x_1890_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1885_, v_es_1888_, v___x_1893_, v___x_1894_, v_x_1887_);
return v___x_1895_;
}
}
else
{
size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = lean_usize_of_nat(v___x_1890_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1885_, v_es_1888_, v___x_1896_, v___x_1897_, v_x_1887_);
return v___x_1898_;
}
}
}
else
{
lean_object* v_ks_1899_; lean_object* v_vs_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_ks_1899_ = lean_ctor_get(v_x_1886_, 0);
v_vs_1900_ = lean_ctor_get(v_x_1886_, 1);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(v_f_1885_, v_ks_1899_, v_vs_1900_, v___x_1901_, v_x_1887_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(lean_object* v_f_1903_, lean_object* v_as_1904_, size_t v_i_1905_, size_t v_stop_1906_, lean_object* v_b_1907_){
_start:
{
lean_object* v___y_1909_; uint8_t v___x_1913_; 
v___x_1913_ = lean_usize_dec_eq(v_i_1905_, v_stop_1906_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_array_uget_borrowed(v_as_1904_, v_i_1905_);
switch(lean_obj_tag(v___x_1914_))
{
case 0:
{
lean_object* v_key_1915_; lean_object* v_val_1916_; lean_object* v___x_1917_; 
v_key_1915_ = lean_ctor_get(v___x_1914_, 0);
v_val_1916_ = lean_ctor_get(v___x_1914_, 1);
lean_inc(v_f_1903_);
lean_inc(v_val_1916_);
lean_inc(v_key_1915_);
v___x_1917_ = lean_apply_3(v_f_1903_, v_b_1907_, v_key_1915_, v_val_1916_);
v___y_1909_ = v___x_1917_;
goto v___jp_1908_;
}
case 1:
{
lean_object* v_node_1918_; lean_object* v___x_1919_; 
v_node_1918_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_f_1903_);
v___x_1919_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_1903_, v_node_1918_, v_b_1907_);
v___y_1909_ = v___x_1919_;
goto v___jp_1908_;
}
default: 
{
v___y_1909_ = v_b_1907_;
goto v___jp_1908_;
}
}
}
else
{
lean_dec(v_f_1903_);
return v_b_1907_;
}
v___jp_1908_:
{
size_t v___x_1910_; size_t v___x_1911_; 
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1905_, v___x_1910_);
v_i_1905_ = v___x_1911_;
v_b_1907_ = v___y_1909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(lean_object* v_f_1920_, lean_object* v_as_1921_, lean_object* v_i_1922_, lean_object* v_stop_1923_, lean_object* v_b_1924_){
_start:
{
size_t v_i_boxed_1925_; size_t v_stop_boxed_1926_; lean_object* v_res_1927_; 
v_i_boxed_1925_ = lean_unbox_usize(v_i_1922_);
lean_dec(v_i_1922_);
v_stop_boxed_1926_ = lean_unbox_usize(v_stop_1923_);
lean_dec(v_stop_1923_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_1920_, v_as_1921_, v_i_boxed_1925_, v_stop_boxed_1926_, v_b_1924_);
lean_dec_ref(v_as_1921_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(lean_object* v_f_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_1928_, v_x_1929_, v_x_1930_);
lean_dec_ref(v_x_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___lam__0(lean_object* v_f_1932_, lean_object* v_x1_1933_, lean_object* v_x2_1934_, lean_object* v_x3_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_apply_3(v_f_1932_, v_x1_1933_, v_x2_1934_, v_x3_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(lean_object* v_map_1937_, lean_object* v_f_1938_, lean_object* v_init_1939_){
_start:
{
lean_object* v___f_1940_; lean_object* v___x_1941_; 
v___f_1940_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1940_, 0, v_f_1938_);
v___x_1941_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_1940_, v_map_1937_, v_init_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___boxed(lean_object* v_map_1942_, lean_object* v_f_1943_, lean_object* v_init_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(v_map_1942_, v_f_1943_, v_init_1944_);
lean_dec_ref(v_map_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0(lean_object* v_ps_1946_, lean_object* v_k_1947_, lean_object* v_v_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_k_1947_);
lean_ctor_set(v___x_1949_, 1, v_v_1948_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v_ps_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(lean_object* v_m_1952_){
_start:
{
lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___f_1953_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0));
v___x_1954_ = lean_box(0);
v___x_1955_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(v_m_1952_, v___f_1953_, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___boxed(lean_object* v_m_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_1956_);
lean_dec_ref(v_m_1956_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(lean_object* v_s_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_s_1958_);
v___x_1960_ = lean_box(0);
v___x_1961_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(v___x_1959_, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9___boxed(lean_object* v_s_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_s_1962_);
lean_dec_ref(v_s_1962_);
return v_res_1963_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4));
v___x_1972_ = l_Lean_stringToMessageData(v___x_1971_);
return v___x_1972_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(lean_object* v_as_1979_, size_t v_sz_1980_, size_t v_i_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_a_1991_; uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1981_, v_sz_1980_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_b_1982_);
return v___x_1996_;
}
else
{
lean_object* v_a_1997_; lean_object* v_proof_1998_; lean_object* v_priority_1999_; lean_object* v___x_2000_; 
v_a_1997_ = lean_array_uget_borrowed(v_as_1979_, v_i_1981_);
v_proof_1998_ = lean_ctor_get(v_a_1997_, 2);
v_priority_1999_ = lean_ctor_get(v_a_1997_, 4);
lean_inc(v_priority_1999_);
lean_inc_ref(v_proof_1998_);
v___x_2000_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(v_proof_1998_, v_priority_1999_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
if (lean_obj_tag(v_a_2001_) == 1)
{
lean_object* v_val_2002_; lean_object* v_pattern_2003_; lean_object* v___x_2004_; 
v_val_2002_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_val_2002_);
lean_dec_ref_known(v_a_2001_, 1);
v_pattern_2003_ = lean_ctor_get(v_val_2002_, 0);
lean_inc_ref(v_pattern_2003_);
v___x_2004_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_1982_, v_pattern_2003_, v_val_2002_);
v_a_1991_ = v___x_2004_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2005_; lean_object* v___y_2007_; 
lean_dec(v_a_2001_);
v___x_2005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1);
switch(lean_obj_tag(v_proof_1998_))
{
case 0:
{
lean_object* v_declName_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_declName_2018_ = lean_ctor_get(v_proof_1998_, 0);
v___x_2019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3);
lean_inc(v_declName_2018_);
v___x_2020_ = l_Lean_MessageData_ofName(v_declName_2018_);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___y_2007_ = v___x_2021_;
goto v___jp_2006_;
}
case 1:
{
lean_object* v_fvarId_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_fvarId_2022_ = lean_ctor_get(v_proof_1998_, 0);
v___x_2023_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5);
lean_inc(v_fvarId_2022_);
v___x_2024_ = l_Lean_mkFVar(v_fvarId_2022_);
v___x_2025_ = l_Lean_MessageData_ofExpr(v___x_2024_);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2023_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___y_2007_ = v___x_2026_;
goto v___jp_2006_;
}
default: 
{
lean_object* v_ref_2027_; lean_object* v_proof_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_ref_2027_ = lean_ctor_get(v_proof_1998_, 1);
v_proof_2028_ = lean_ctor_get(v_proof_1998_, 2);
v___x_2029_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7);
lean_inc(v_ref_2027_);
v___x_2030_ = l_Lean_MessageData_ofSyntax(v_ref_2027_);
v___x_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2029_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_inc_ref(v_proof_2028_);
v___x_2034_ = l_Lean_MessageData_ofExpr(v_proof_2028_);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___y_2007_ = v___x_2035_;
goto v___jp_2006_;
}
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2005_);
lean_ctor_set(v___x_2008_, 1, v___y_2007_);
v___x_2009_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_2008_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_dec_ref_known(v___x_2009_, 1);
v_a_1991_ = v_b_1982_;
goto v___jp_1990_;
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec_ref(v_b_1982_);
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_b_1982_);
v_a_2036_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2000_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2000_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
v___jp_1990_:
{
size_t v___x_1992_; size_t v___x_1993_; 
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1981_, v___x_1992_);
v_i_1981_ = v___x_1993_;
v_b_1982_ = v_a_1991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(lean_object* v_as_2044_, lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
size_t v_sz_boxed_2055_; size_t v_i_boxed_2056_; lean_object* v_res_2057_; 
v_sz_boxed_2055_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2056_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_as_2044_, v_sz_boxed_2055_, v_i_boxed_2056_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec_ref(v_as_2044_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(lean_object* v_keys_2058_, lean_object* v_vals_2059_, lean_object* v_i_2060_, lean_object* v_k_2061_){
_start:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = lean_array_get_size(v_keys_2058_);
v___x_2063_ = lean_nat_dec_lt(v_i_2060_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec(v_i_2060_);
v___x_2064_ = lean_box(0);
return v___x_2064_;
}
else
{
lean_object* v_k_x27_2065_; uint8_t v___x_2066_; 
v_k_x27_2065_ = lean_array_fget_borrowed(v_keys_2058_, v_i_2060_);
v___x_2066_ = lean_name_eq(v_k_2061_, v_k_x27_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_add(v_i_2060_, v___x_2067_);
lean_dec(v_i_2060_);
v_i_2060_ = v___x_2068_;
goto _start;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_array_fget_borrowed(v_vals_2059_, v_i_2060_);
lean_dec(v_i_2060_);
lean_inc(v___x_2070_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg___boxed(lean_object* v_keys_2072_, lean_object* v_vals_2073_, lean_object* v_i_2074_, lean_object* v_k_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(v_keys_2072_, v_vals_2073_, v_i_2074_, v_k_2075_);
lean_dec(v_k_2075_);
lean_dec_ref(v_vals_2073_);
lean_dec_ref(v_keys_2072_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(lean_object* v_x_2077_, size_t v_x_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_object* v_es_2080_; lean_object* v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; lean_object* v_j_2085_; lean_object* v___x_2086_; 
v_es_2080_ = lean_ctor_get(v_x_2077_, 0);
v___x_2081_ = lean_box(2);
v___x_2082_ = ((size_t)5ULL);
v___x_2083_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_2084_ = lean_usize_land(v_x_2078_, v___x_2083_);
v_j_2085_ = lean_usize_to_nat(v___x_2084_);
v___x_2086_ = lean_array_get_borrowed(v___x_2081_, v_es_2080_, v_j_2085_);
lean_dec(v_j_2085_);
switch(lean_obj_tag(v___x_2086_))
{
case 0:
{
lean_object* v_key_2087_; lean_object* v_val_2088_; uint8_t v___x_2089_; 
v_key_2087_ = lean_ctor_get(v___x_2086_, 0);
v_val_2088_ = lean_ctor_get(v___x_2086_, 1);
v___x_2089_ = lean_name_eq(v_x_2079_, v_key_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_box(0);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; 
lean_inc(v_val_2088_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_val_2088_);
return v___x_2091_;
}
}
case 1:
{
lean_object* v_node_2092_; size_t v___x_2093_; 
v_node_2092_ = lean_ctor_get(v___x_2086_, 0);
v___x_2093_ = lean_usize_shift_right(v_x_2078_, v___x_2082_);
v_x_2077_ = v_node_2092_;
v_x_2078_ = v___x_2093_;
goto _start;
}
default: 
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
}
}
else
{
lean_object* v_ks_2096_; lean_object* v_vs_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_ks_2096_ = lean_ctor_get(v_x_2077_, 0);
v_vs_2097_ = lean_ctor_get(v_x_2077_, 1);
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(v_ks_2096_, v_vs_2097_, v___x_2098_, v_x_2079_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg___boxed(lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
size_t v_x_27997__boxed_2103_; lean_object* v_res_2104_; 
v_x_27997__boxed_2103_ = lean_unbox_usize(v_x_2101_);
lean_dec(v_x_2101_);
v_res_2104_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2100_, v_x_27997__boxed_2103_, v_x_2102_);
lean_dec(v_x_2102_);
lean_dec_ref(v_x_2100_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
uint64_t v___y_2108_; 
if (lean_obj_tag(v_x_2106_) == 0)
{
uint64_t v___x_2111_; 
v___x_2111_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2108_ = v___x_2111_;
goto v___jp_2107_;
}
else
{
uint64_t v_hash_2112_; 
v_hash_2112_ = lean_ctor_get_uint64(v_x_2106_, sizeof(void*)*2);
v___y_2108_ = v_hash_2112_;
goto v___jp_2107_;
}
v___jp_2107_:
{
size_t v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_uint64_to_usize(v___y_2108_);
v___x_2110_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2105_, v___x_2109_, v_x_2106_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg___boxed(lean_object* v_x_2113_, lean_object* v_x_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2113_, v_x_2114_);
lean_dec(v_x_2114_);
lean_dec_ref(v_x_2113_);
return v_res_2115_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(lean_object* v_a_2122_, lean_object* v_as_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_snd_2135_; uint8_t v___x_2139_; 
v___x_2139_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec(v_a_2122_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_b_2126_);
return v___x_2140_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2141_ = lean_array_uget_borrowed(v_as_2123_, v_i_2125_);
v___x_2142_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_2141_);
v___x_2143_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(v_a_2141_, v___x_2142_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2145_; lean_object* v_pattern_2146_; lean_object* v___x_2147_; 
v_val_2145_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_a_2144_, 1);
v_pattern_2146_ = lean_ctor_get(v_val_2145_, 0);
lean_inc_ref(v_pattern_2146_);
v___x_2147_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_2126_, v_pattern_2146_, v_val_2145_);
v_snd_2135_ = v___x_2147_;
goto v___jp_2134_;
}
else
{
lean_dec(v_a_2144_);
v_snd_2135_ = v_b_2126_;
goto v___jp_2134_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2185_; 
v_a_2148_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2150_ = v___x_2143_;
v_isShared_2151_ = v_isSharedCheck_2185_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2143_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2185_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
uint8_t v___y_2153_; uint8_t v___x_2183_; 
v___x_2183_ = l_Lean_Exception_isInterrupt(v_a_2148_);
if (v___x_2183_ == 0)
{
uint8_t v___x_2184_; 
lean_inc(v_a_2148_);
v___x_2184_ = l_Lean_Exception_isRuntime(v_a_2148_);
v___y_2153_ = v___x_2184_;
goto v___jp_2152_;
}
else
{
v___y_2153_ = v___x_2183_;
goto v___jp_2152_;
}
v___jp_2152_:
{
if (v___y_2153_ == 0)
{
lean_object* v_options_2154_; uint8_t v_hasTrace_2155_; 
lean_del_object(v___x_2150_);
v_options_2154_ = lean_ctor_get(v___y_2131_, 2);
v_hasTrace_2155_ = lean_ctor_get_uint8(v_options_2154_, sizeof(void*)*1);
if (v_hasTrace_2155_ == 0)
{
lean_dec(v_a_2148_);
v_snd_2135_ = v_b_2126_;
goto v___jp_2134_;
}
else
{
lean_object* v_inheritedTraceOptions_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_inheritedTraceOptions_2156_ = lean_ctor_get(v___y_2131_, 13);
v___x_2157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3));
v___x_2158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
v___x_2159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2156_, v_options_2154_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_dec(v_a_2148_);
v_snd_2135_ = v_b_2126_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1);
lean_inc(v_a_2122_);
v___x_2161_ = l_Lean_MessageData_ofName(v_a_2122_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
lean_inc(v_a_2141_);
v___x_2165_ = l_Lean_MessageData_ofName(v_a_2141_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_Exception_toMessageData(v_a_2148_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_2157_, v___x_2170_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_dec_ref_known(v___x_2171_, 1);
v_snd_2135_ = v_b_2126_;
goto v___jp_2134_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_b_2126_);
lean_dec(v_a_2122_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
else
{
lean_object* v___x_2181_; 
lean_dec_ref(v_b_2126_);
lean_dec(v_a_2122_);
if (v_isShared_2151_ == 0)
{
v___x_2181_ = v___x_2150_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2148_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
v___jp_2134_:
{
size_t v___x_2136_; size_t v___x_2137_; 
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2125_, v___x_2136_);
v_i_2125_ = v___x_2137_;
v_b_2126_ = v_snd_2135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___boxed(lean_object* v_a_2186_, lean_object* v_as_2187_, lean_object* v_sz_2188_, lean_object* v_i_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
size_t v_sz_boxed_2198_; size_t v_i_boxed_2199_; lean_object* v_res_2200_; 
v_sz_boxed_2198_ = lean_unbox_usize(v_sz_2188_);
lean_dec(v_sz_2188_);
v_i_boxed_2199_ = lean_unbox_usize(v_i_2189_);
lean_dec(v_i_2189_);
v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_a_2186_, v_as_2187_, v_sz_boxed_2198_, v_i_boxed_2199_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_as_2187_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(lean_object* v_simpThms_2201_, lean_object* v_as_x27_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
if (lean_obj_tag(v_as_x27_2202_) == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_b_2203_);
return v___x_2211_;
}
else
{
lean_object* v_head_2212_; lean_object* v_tail_2213_; lean_object* v_eqThms_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v_toUnfoldThms_2227_; lean_object* v___x_2228_; 
v_head_2212_ = lean_ctor_get(v_as_x27_2202_, 0);
v_tail_2213_ = lean_ctor_get(v_as_x27_2202_, 1);
v_toUnfoldThms_2227_ = lean_ctor_get(v_simpThms_2201_, 5);
v___x_2228_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_toUnfoldThms_2227_, v_head_2212_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2229_; 
lean_inc(v_head_2212_);
v___x_2229_ = l_Lean_Meta_getEqnsFor_x3f(v_head_2212_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
if (lean_obj_tag(v_a_2230_) == 1)
{
lean_object* v_val_2231_; 
v_val_2231_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v_a_2230_, 1);
v_eqThms_2215_ = v_val_2231_;
v___y_2216_ = v___y_2204_;
v___y_2217_ = v___y_2205_;
v___y_2218_ = v___y_2206_;
v___y_2219_ = v___y_2207_;
v___y_2220_ = v___y_2208_;
v___y_2221_ = v___y_2209_;
goto v___jp_2214_;
}
else
{
lean_dec(v_a_2230_);
v_as_x27_2202_ = v_tail_2213_;
goto _start;
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_b_2203_);
v_a_2233_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2229_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2229_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_val_2241_; 
v_val_2241_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v___x_2228_, 1);
v_eqThms_2215_ = v_val_2241_;
v___y_2216_ = v___y_2204_;
v___y_2217_ = v___y_2205_;
v___y_2218_ = v___y_2206_;
v___y_2219_ = v___y_2207_;
v___y_2220_ = v___y_2208_;
v___y_2221_ = v___y_2209_;
goto v___jp_2214_;
}
v___jp_2214_:
{
size_t v_sz_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v_sz_2222_ = lean_array_size(v_eqThms_2215_);
v___x_2223_ = ((size_t)0ULL);
lean_inc(v_head_2212_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_head_2212_, v_eqThms_2215_, v_sz_2222_, v___x_2223_, v_b_2203_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec_ref(v_eqThms_2215_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v_as_x27_2202_ = v_tail_2213_;
v_b_2203_ = v_a_2225_;
goto _start;
}
else
{
return v___x_2224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg___boxed(lean_object* v_simpThms_2242_, lean_object* v_as_x27_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2242_, v_as_x27_2243_, v_b_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v_as_x27_2243_);
lean_dec_ref(v_simpThms_2242_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(lean_object* v_database_2262_, lean_object* v_simpThms_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_specs_2271_; lean_object* v_erased_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2331_; 
v_specs_2271_ = lean_ctor_get(v_database_2262_, 0);
v_erased_2272_ = lean_ctor_get(v_database_2262_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_database_2262_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2274_ = v_database_2262_;
v_isShared_2275_ = v_isSharedCheck_2331_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_erased_2272_);
lean_inc(v_specs_2271_);
lean_dec(v_database_2262_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2331_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___f_2276_; lean_object* v_specs_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; size_t v_sz_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___f_2276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1));
v_specs_2277_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0, &l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0);
v___x_2278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2));
v___x_2279_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2276_, v_specs_2271_, v___x_2278_);
lean_dec_ref(v_specs_2271_);
v_sz_2280_ = lean_array_size(v___x_2279_);
v___x_2281_ = ((size_t)0ULL);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v___x_2279_, v_sz_2280_, v___x_2281_, v_specs_2277_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v___x_2279_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_post_2284_; lean_object* v_toUnfold_2285_; lean_object* v_erased_2286_; lean_object* v___f_2287_; lean_object* v___x_2288_; size_t v_sz_2289_; lean_object* v___x_2290_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v_post_2284_ = lean_ctor_get(v_simpThms_2263_, 1);
v_toUnfold_2285_ = lean_ctor_get(v_simpThms_2263_, 3);
v_erased_2286_ = lean_ctor_get(v_simpThms_2263_, 4);
v___f_2287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4));
v___x_2288_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2287_, v_post_2284_, v___x_2278_);
v_sz_2289_ = lean_array_size(v___x_2288_);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v___x_2288_, v_sz_2289_, v___x_2281_, v_a_2283_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v___x_2288_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_toUnfold_2285_);
v___x_2293_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2263_, v___x_2292_, v_a_2291_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2306_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___f_2298_; lean_object* v_erased_2299_; lean_object* v___x_2301_; 
v___f_2298_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5));
v_erased_2299_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_2298_, v_erased_2286_, v_erased_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v_erased_2299_);
lean_ctor_set(v___x_2274_, 0, v_a_2294_);
v___x_2301_ = v___x_2274_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_erased_2299_);
v___x_2301_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2303_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2301_);
v___x_2303_ = v___x_2296_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_del_object(v___x_2274_);
lean_dec_ref(v_erased_2272_);
v_a_2307_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2293_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2293_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_del_object(v___x_2274_);
lean_dec_ref(v_erased_2272_);
v_a_2315_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2290_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2290_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_del_object(v___x_2274_);
lean_dec_ref(v_erased_2272_);
v_a_2323_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2282_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2282_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object* v_database_2332_, lean_object* v_simpThms_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(v_database_2332_, v_simpThms_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec_ref(v_simpThms_2333_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(v_x_2343_, v_x_2344_, v_x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(lean_object* v_cls_2347_, lean_object* v_msg_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_2347_, v_msg_2348_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___boxed(lean_object* v_cls_2357_, lean_object* v_msg_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(v_cls_2357_, v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(lean_object* v_00_u03b2_2367_, lean_object* v_x_2368_, lean_object* v_x_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_2368_, v_x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___boxed(lean_object* v_00_u03b2_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(v_00_u03b2_2371_, v_x_2372_, v_x_2373_);
lean_dec(v_x_2373_);
lean_dec_ref(v_x_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(lean_object* v_00_u03c3_2375_, lean_object* v_00_u03b1_2376_, lean_object* v_f_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_2377_, v_x_2378_, v_x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___boxed(lean_object* v_00_u03c3_2381_, lean_object* v_00_u03b1_2382_, lean_object* v_f_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(v_00_u03c3_2381_, v_00_u03b1_2382_, v_f_2383_, v_x_2384_, v_x_2385_);
lean_dec_ref(v_x_2385_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(lean_object* v_map_2387_, lean_object* v_f_2388_, lean_object* v_init_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2388_, v_map_2387_, v_init_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg___boxed(lean_object* v_map_2391_, lean_object* v_f_2392_, lean_object* v_init_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(v_map_2391_, v_f_2392_, v_init_2393_);
lean_dec_ref(v_map_2391_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(lean_object* v_00_u03c3_2395_, lean_object* v_00_u03b2_2396_, lean_object* v_map_2397_, lean_object* v_f_2398_, lean_object* v_init_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2398_, v_map_2397_, v_init_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___boxed(lean_object* v_00_u03c3_2401_, lean_object* v_00_u03b2_2402_, lean_object* v_map_2403_, lean_object* v_f_2404_, lean_object* v_init_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(v_00_u03c3_2401_, v_00_u03b2_2402_, v_map_2403_, v_f_2404_, v_init_2405_);
lean_dec_ref(v_map_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(lean_object* v_simpThms_2407_, lean_object* v_as_2408_, lean_object* v_as_x27_2409_, lean_object* v_b_2410_, lean_object* v_a_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_2407_, v_as_x27_2409_, v_b_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___boxed(lean_object* v_simpThms_2420_, lean_object* v_as_2421_, lean_object* v_as_x27_2422_, lean_object* v_b_2423_, lean_object* v_a_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(v_simpThms_2420_, v_as_2421_, v_as_x27_2422_, v_b_2423_, v_a_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v_as_x27_2422_);
lean_dec(v_as_2421_);
lean_dec_ref(v_simpThms_2420_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(lean_object* v_map_2433_, lean_object* v_f_2434_, lean_object* v_init_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2434_, v_map_2433_, v_init_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg___boxed(lean_object* v_map_2437_, lean_object* v_f_2438_, lean_object* v_init_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(v_map_2437_, v_f_2438_, v_init_2439_);
lean_dec_ref(v_map_2437_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(lean_object* v_00_u03c3_2441_, lean_object* v_00_u03b2_2442_, lean_object* v_map_2443_, lean_object* v_f_2444_, lean_object* v_init_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2444_, v_map_2443_, v_init_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___boxed(lean_object* v_00_u03c3_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_map_2449_, lean_object* v_f_2450_, lean_object* v_init_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(v_00_u03c3_2447_, v_00_u03b2_2448_, v_map_2449_, v_f_2450_, v_init_2451_);
lean_dec_ref(v_map_2449_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(lean_object* v_00_u03b2_2453_, lean_object* v_x_2454_, size_t v_x_2455_, size_t v_x_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_2454_, v_x_2455_, v_x_2456_, v_x_2457_, v_x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
size_t v_x_28508__boxed_2466_; size_t v_x_28509__boxed_2467_; lean_object* v_res_2468_; 
v_x_28508__boxed_2466_ = lean_unbox_usize(v_x_2462_);
lean_dec(v_x_2462_);
v_x_28509__boxed_2467_ = lean_unbox_usize(v_x_2463_);
lean_dec(v_x_2463_);
v_res_2468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(v_00_u03b2_2460_, v_x_2461_, v_x_28508__boxed_2466_, v_x_28509__boxed_2467_, v_x_2464_, v_x_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(lean_object* v_00_u03b2_2469_, lean_object* v_x_2470_, size_t v_x_2471_, lean_object* v_x_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_2470_, v_x_2471_, v_x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___boxed(lean_object* v_00_u03b2_2474_, lean_object* v_x_2475_, lean_object* v_x_2476_, lean_object* v_x_2477_){
_start:
{
size_t v_x_28525__boxed_2478_; lean_object* v_res_2479_; 
v_x_28525__boxed_2478_ = lean_unbox_usize(v_x_2476_);
lean_dec(v_x_2476_);
v_res_2479_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(v_00_u03b2_2474_, v_x_2475_, v_x_28525__boxed_2478_, v_x_2477_);
lean_dec(v_x_2477_);
lean_dec_ref(v_x_2475_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(lean_object* v_00_u03b1_2480_, lean_object* v_00_u03c3_2481_, lean_object* v_f_2482_, lean_object* v_as_2483_, size_t v_i_2484_, size_t v_stop_2485_, lean_object* v_b_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_2482_, v_as_2483_, v_i_2484_, v_stop_2485_, v_b_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2488_, lean_object* v_00_u03c3_2489_, lean_object* v_f_2490_, lean_object* v_as_2491_, lean_object* v_i_2492_, lean_object* v_stop_2493_, lean_object* v_b_2494_){
_start:
{
size_t v_i_boxed_2495_; size_t v_stop_boxed_2496_; lean_object* v_res_2497_; 
v_i_boxed_2495_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_stop_boxed_2496_ = lean_unbox_usize(v_stop_2493_);
lean_dec(v_stop_2493_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(v_00_u03b1_2488_, v_00_u03c3_2489_, v_f_2490_, v_as_2491_, v_i_boxed_2495_, v_stop_boxed_2496_, v_b_2494_);
lean_dec_ref(v_as_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03c3_2499_, lean_object* v_f_2500_, lean_object* v_as_2501_, size_t v_i_2502_, size_t v_stop_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_2500_, v_as_2501_, v_i_2502_, v_stop_2503_, v_b_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2506_, lean_object* v_00_u03c3_2507_, lean_object* v_f_2508_, lean_object* v_as_2509_, lean_object* v_i_2510_, lean_object* v_stop_2511_, lean_object* v_b_2512_){
_start:
{
size_t v_i_boxed_2513_; size_t v_stop_boxed_2514_; lean_object* v_res_2515_; 
v_i_boxed_2513_ = lean_unbox_usize(v_i_2510_);
lean_dec(v_i_2510_);
v_stop_boxed_2514_ = lean_unbox_usize(v_stop_2511_);
lean_dec(v_stop_2511_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(v_00_u03b1_2506_, v_00_u03c3_2507_, v_f_2508_, v_as_2509_, v_i_boxed_2513_, v_stop_boxed_2514_, v_b_2512_);
lean_dec_ref(v_as_2509_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(lean_object* v_00_u03c3_2516_, lean_object* v_00_u03b1_2517_, lean_object* v_00_u03b2_2518_, lean_object* v_f_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2519_, v_x_2520_, v_x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___boxed(lean_object* v_00_u03c3_2523_, lean_object* v_00_u03b1_2524_, lean_object* v_00_u03b2_2525_, lean_object* v_f_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(v_00_u03c3_2523_, v_00_u03b1_2524_, v_00_u03b2_2525_, v_f_2526_, v_x_2527_, v_x_2528_);
lean_dec_ref(v_x_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(lean_object* v_00_u03b2_2530_, lean_object* v_m_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___boxed(lean_object* v_00_u03b2_2533_, lean_object* v_m_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(v_00_u03b2_2533_, v_m_2534_);
lean_dec_ref(v_m_2534_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2536_, lean_object* v_n_2537_, lean_object* v_k_2538_, lean_object* v_v_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_n_2537_, v_k_2538_, v_v_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2541_, size_t v_depth_2542_, lean_object* v_keys_2543_, lean_object* v_vals_2544_, lean_object* v_heq_2545_, lean_object* v_i_2546_, lean_object* v_entries_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_depth_2542_, v_keys_2543_, v_vals_2544_, v_i_2546_, v_entries_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2549_, lean_object* v_depth_2550_, lean_object* v_keys_2551_, lean_object* v_vals_2552_, lean_object* v_heq_2553_, lean_object* v_i_2554_, lean_object* v_entries_2555_){
_start:
{
size_t v_depth_boxed_2556_; lean_object* v_res_2557_; 
v_depth_boxed_2556_ = lean_unbox_usize(v_depth_2550_);
lean_dec(v_depth_2550_);
v_res_2557_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(v_00_u03b2_2549_, v_depth_boxed_2556_, v_keys_2551_, v_vals_2552_, v_heq_2553_, v_i_2554_, v_entries_2555_);
lean_dec_ref(v_vals_2552_);
lean_dec_ref(v_keys_2551_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(v_x_2559_, v_x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(v_00_u03b2_2562_, v_x_2563_, v_x_2564_);
lean_dec(v_x_2564_);
lean_dec_ref(v_x_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(v_x_2567_, v_x_2568_, v_x_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13(lean_object* v_00_u03b2_2571_, lean_object* v_keys_2572_, lean_object* v_vals_2573_, lean_object* v_heq_2574_, lean_object* v_i_2575_, lean_object* v_k_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(v_keys_2572_, v_vals_2573_, v_i_2575_, v_k_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___boxed(lean_object* v_00_u03b2_2578_, lean_object* v_keys_2579_, lean_object* v_vals_2580_, lean_object* v_heq_2581_, lean_object* v_i_2582_, lean_object* v_k_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13(v_00_u03b2_2578_, v_keys_2579_, v_vals_2580_, v_heq_2581_, v_i_2582_, v_k_2583_);
lean_dec(v_k_2583_);
lean_dec_ref(v_vals_2580_);
lean_dec_ref(v_keys_2579_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(lean_object* v_00_u03b1_2585_, lean_object* v_00_u03b2_2586_, lean_object* v_00_u03c3_2587_, lean_object* v_f_2588_, lean_object* v_as_2589_, size_t v_i_2590_, size_t v_stop_2591_, lean_object* v_b_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_2588_, v_as_2589_, v_i_2590_, v_stop_2591_, v_b_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(lean_object* v_00_u03b1_2594_, lean_object* v_00_u03b2_2595_, lean_object* v_00_u03c3_2596_, lean_object* v_f_2597_, lean_object* v_as_2598_, lean_object* v_i_2599_, lean_object* v_stop_2600_, lean_object* v_b_2601_){
_start:
{
size_t v_i_boxed_2602_; size_t v_stop_boxed_2603_; lean_object* v_res_2604_; 
v_i_boxed_2602_ = lean_unbox_usize(v_i_2599_);
lean_dec(v_i_2599_);
v_stop_boxed_2603_ = lean_unbox_usize(v_stop_2600_);
lean_dec(v_stop_2600_);
v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(v_00_u03b1_2594_, v_00_u03b2_2595_, v_00_u03c3_2596_, v_f_2597_, v_as_2598_, v_i_boxed_2602_, v_stop_boxed_2603_, v_b_2601_);
lean_dec_ref(v_as_2598_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20(lean_object* v_00_u03c3_2605_, lean_object* v_00_u03b1_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_f_2608_, lean_object* v_keys_2609_, lean_object* v_vals_2610_, lean_object* v_heq_2611_, lean_object* v_i_2612_, lean_object* v_acc_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(v_f_2608_, v_keys_2609_, v_vals_2610_, v_i_2612_, v_acc_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___boxed(lean_object* v_00_u03c3_2615_, lean_object* v_00_u03b1_2616_, lean_object* v_00_u03b2_2617_, lean_object* v_f_2618_, lean_object* v_keys_2619_, lean_object* v_vals_2620_, lean_object* v_heq_2621_, lean_object* v_i_2622_, lean_object* v_acc_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20(v_00_u03c3_2615_, v_00_u03b1_2616_, v_00_u03b2_2617_, v_f_2618_, v_keys_2619_, v_vals_2620_, v_heq_2621_, v_i_2622_, v_acc_2623_);
lean_dec_ref(v_vals_2620_);
lean_dec_ref(v_keys_2619_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25(lean_object* v_00_u03c3_2625_, lean_object* v_00_u03b2_2626_, lean_object* v_map_2627_, lean_object* v_f_2628_, lean_object* v_init_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(v_map_2627_, v_f_2628_, v_init_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___boxed(lean_object* v_00_u03c3_2631_, lean_object* v_00_u03b2_2632_, lean_object* v_map_2633_, lean_object* v_f_2634_, lean_object* v_init_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25(v_00_u03c3_2631_, v_00_u03b2_2632_, v_map_2633_, v_f_2634_, v_init_2635_);
lean_dec_ref(v_map_2633_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13(lean_object* v_00_u03b2_2637_, lean_object* v_x_2638_, lean_object* v_x_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(v_x_2638_, v_x_2639_, v_x_2640_, v_x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(lean_object* v_00_u03b2_2643_, lean_object* v_x_2644_, size_t v_x_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(v_x_2644_, v_x_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___boxed(lean_object* v_00_u03b2_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_, lean_object* v_x_2651_){
_start:
{
size_t v_x_28588__boxed_2652_; lean_object* v_res_2653_; 
v_x_28588__boxed_2652_ = lean_unbox_usize(v_x_2650_);
lean_dec(v_x_2650_);
v_res_2653_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(v_00_u03b2_2648_, v_x_2649_, v_x_28588__boxed_2652_, v_x_2651_);
lean_dec(v_x_2651_);
lean_dec_ref(v_x_2649_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19(lean_object* v_00_u03b2_2654_, lean_object* v_x_2655_, size_t v_x_2656_, size_t v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_x_2655_, v_x_2656_, v_x_2657_, v_x_2658_, v_x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___boxed(lean_object* v_00_u03b2_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
size_t v_x_28599__boxed_2667_; size_t v_x_28600__boxed_2668_; lean_object* v_res_2669_; 
v_x_28599__boxed_2667_ = lean_unbox_usize(v_x_2663_);
lean_dec(v_x_2663_);
v_x_28600__boxed_2668_ = lean_unbox_usize(v_x_2664_);
lean_dec(v_x_2664_);
v_res_2669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19(v_00_u03b2_2661_, v_x_2662_, v_x_28599__boxed_2667_, v_x_28600__boxed_2668_, v_x_2665_, v_x_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg(lean_object* v_map_2670_, lean_object* v_f_2671_, lean_object* v_init_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2671_, v_map_2670_, v_init_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg___boxed(lean_object* v_map_2674_, lean_object* v_f_2675_, lean_object* v_init_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg(v_map_2674_, v_f_2675_, v_init_2676_);
lean_dec_ref(v_map_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33(lean_object* v_00_u03c3_2678_, lean_object* v_00_u03b2_2679_, lean_object* v_map_2680_, lean_object* v_f_2681_, lean_object* v_init_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_2681_, v_map_2680_, v_init_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___boxed(lean_object* v_00_u03c3_2684_, lean_object* v_00_u03b2_2685_, lean_object* v_map_2686_, lean_object* v_f_2687_, lean_object* v_init_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33(v_00_u03c3_2684_, v_00_u03b2_2685_, v_map_2686_, v_f_2687_, v_init_2688_);
lean_dec_ref(v_map_2686_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(lean_object* v_00_u03b2_2690_, lean_object* v_keys_2691_, lean_object* v_vals_2692_, lean_object* v_heq_2693_, lean_object* v_i_2694_, lean_object* v_k_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(v_keys_2691_, v_vals_2692_, v_i_2694_, v_k_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___boxed(lean_object* v_00_u03b2_2697_, lean_object* v_keys_2698_, lean_object* v_vals_2699_, lean_object* v_heq_2700_, lean_object* v_i_2701_, lean_object* v_k_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(v_00_u03b2_2697_, v_keys_2698_, v_vals_2699_, v_heq_2700_, v_i_2701_, v_k_2702_);
lean_dec(v_k_2702_);
lean_dec_ref(v_vals_2699_);
lean_dec_ref(v_keys_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28(lean_object* v_00_u03b2_2704_, lean_object* v_n_2705_, lean_object* v_k_2706_, lean_object* v_v_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(v_n_2705_, v_k_2706_, v_v_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29(lean_object* v_00_u03b2_2709_, size_t v_depth_2710_, lean_object* v_keys_2711_, lean_object* v_vals_2712_, lean_object* v_heq_2713_, lean_object* v_i_2714_, lean_object* v_entries_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(v_depth_2710_, v_keys_2711_, v_vals_2712_, v_i_2714_, v_entries_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___boxed(lean_object* v_00_u03b2_2717_, lean_object* v_depth_2718_, lean_object* v_keys_2719_, lean_object* v_vals_2720_, lean_object* v_heq_2721_, lean_object* v_i_2722_, lean_object* v_entries_2723_){
_start:
{
size_t v_depth_boxed_2724_; lean_object* v_res_2725_; 
v_depth_boxed_2724_ = lean_unbox_usize(v_depth_2718_);
lean_dec(v_depth_2718_);
v_res_2725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29(v_00_u03b2_2717_, v_depth_boxed_2724_, v_keys_2719_, v_vals_2720_, v_heq_2721_, v_i_2722_, v_entries_2723_);
lean_dec_ref(v_vals_2720_);
lean_dec_ref(v_keys_2719_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34(lean_object* v_x_2726_, lean_object* v_keys_2727_, lean_object* v_v_2728_, lean_object* v_k_2729_, lean_object* v_as_2730_, lean_object* v_k_2731_, lean_object* v_x_2732_, lean_object* v_x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(v_x_2726_, v_keys_2727_, v_v_2728_, v_k_2729_, v_as_2730_, v_k_2731_, v_x_2732_, v_x_2733_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___boxed(lean_object* v_x_2737_, lean_object* v_keys_2738_, lean_object* v_v_2739_, lean_object* v_k_2740_, lean_object* v_as_2741_, lean_object* v_k_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34(v_x_2737_, v_keys_2738_, v_v_2739_, v_k_2740_, v_as_2741_, v_k_2742_, v_x_2743_, v_x_2744_, v_x_2745_, v_x_2746_);
lean_dec_ref(v_k_2742_);
lean_dec_ref(v_keys_2738_);
lean_dec(v_x_2737_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34(lean_object* v_00_u03b2_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(v_x_2749_, v_x_2750_, v_x_2751_, v_x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(lean_object* v_xs_2754_, lean_object* v_j_2755_){
_start:
{
lean_object* v_zero_2756_; uint8_t v_isZero_2757_; 
v_zero_2756_ = lean_unsigned_to_nat(0u);
v_isZero_2757_ = lean_nat_dec_eq(v_j_2755_, v_zero_2756_);
if (v_isZero_2757_ == 1)
{
lean_dec(v_j_2755_);
return v_xs_2754_;
}
else
{
lean_object* v_one_2758_; lean_object* v_n_2759_; lean_object* v___x_2760_; lean_object* v_priority_2761_; lean_object* v___x_2762_; lean_object* v_priority_2763_; uint8_t v___x_2764_; 
v_one_2758_ = lean_unsigned_to_nat(1u);
v_n_2759_ = lean_nat_sub(v_j_2755_, v_one_2758_);
v___x_2760_ = lean_array_fget_borrowed(v_xs_2754_, v_n_2759_);
v_priority_2761_ = lean_ctor_get(v___x_2760_, 3);
v___x_2762_ = lean_array_fget_borrowed(v_xs_2754_, v_j_2755_);
v_priority_2763_ = lean_ctor_get(v___x_2762_, 3);
v___x_2764_ = lean_nat_dec_lt(v_priority_2761_, v_priority_2763_);
if (v___x_2764_ == 0)
{
lean_dec(v_n_2759_);
lean_dec(v_j_2755_);
return v_xs_2754_;
}
else
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_array_fswap(v_xs_2754_, v_j_2755_, v_n_2759_);
lean_dec(v_j_2755_);
v_xs_2754_ = v___x_2765_;
v_j_2755_ = v_n_2759_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(lean_object* v_xs_2767_, lean_object* v_i_2768_, lean_object* v_fuel_2769_){
_start:
{
lean_object* v_zero_2770_; uint8_t v_isZero_2771_; 
v_zero_2770_ = lean_unsigned_to_nat(0u);
v_isZero_2771_ = lean_nat_dec_eq(v_fuel_2769_, v_zero_2770_);
if (v_isZero_2771_ == 1)
{
lean_dec(v_fuel_2769_);
lean_dec(v_i_2768_);
return v_xs_2767_;
}
else
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = lean_array_get_size(v_xs_2767_);
v___x_2773_ = lean_nat_dec_lt(v_i_2768_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_dec(v_fuel_2769_);
lean_dec(v_i_2768_);
return v_xs_2767_;
}
else
{
lean_object* v_one_2774_; lean_object* v_n_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_one_2774_ = lean_unsigned_to_nat(1u);
v_n_2775_ = lean_nat_sub(v_fuel_2769_, v_one_2774_);
lean_dec(v_fuel_2769_);
lean_inc(v_i_2768_);
v___x_2776_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(v_xs_2767_, v_i_2768_);
v___x_2777_ = lean_nat_add(v_i_2768_, v_one_2774_);
lean_dec(v_i_2768_);
v_xs_2767_ = v___x_2776_;
v_i_2768_ = v___x_2777_;
v_fuel_2769_ = v_n_2775_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2779_, lean_object* v_i_2780_, lean_object* v_k_2781_){
_start:
{
lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = lean_array_get_size(v_keys_2779_);
v___x_2783_ = lean_nat_dec_lt(v_i_2780_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_dec_ref(v_k_2781_);
lean_dec(v_i_2780_);
return v___x_2783_;
}
else
{
lean_object* v_k_x27_2784_; uint8_t v___x_2785_; 
v_k_x27_2784_ = lean_array_fget_borrowed(v_keys_2779_, v_i_2780_);
lean_inc(v_k_x27_2784_);
lean_inc_ref(v_k_2781_);
v___x_2785_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_k_2781_, v_k_x27_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = lean_nat_add(v_i_2780_, v___x_2786_);
lean_dec(v_i_2780_);
v_i_2780_ = v___x_2787_;
goto _start;
}
else
{
lean_dec_ref(v_k_2781_);
lean_dec(v_i_2780_);
return v___x_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2789_, lean_object* v_i_2790_, lean_object* v_k_2791_){
_start:
{
uint8_t v_res_2792_; lean_object* v_r_2793_; 
v_res_2792_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_keys_2789_, v_i_2790_, v_k_2791_);
lean_dec_ref(v_keys_2789_);
v_r_2793_ = lean_box(v_res_2792_);
return v_r_2793_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(lean_object* v_x_2794_, size_t v_x_2795_, lean_object* v_x_2796_){
_start:
{
if (lean_obj_tag(v_x_2794_) == 0)
{
lean_object* v_es_2797_; lean_object* v___x_2798_; size_t v___x_2799_; size_t v___x_2800_; size_t v___x_2801_; lean_object* v_j_2802_; lean_object* v___x_2803_; 
v_es_2797_ = lean_ctor_get(v_x_2794_, 0);
lean_inc_ref(v_es_2797_);
lean_dec_ref_known(v_x_2794_, 1);
v___x_2798_ = lean_box(2);
v___x_2799_ = ((size_t)5ULL);
v___x_2800_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
v___x_2801_ = lean_usize_land(v_x_2795_, v___x_2800_);
v_j_2802_ = lean_usize_to_nat(v___x_2801_);
v___x_2803_ = lean_array_get(v___x_2798_, v_es_2797_, v_j_2802_);
lean_dec(v_j_2802_);
lean_dec_ref(v_es_2797_);
switch(lean_obj_tag(v___x_2803_))
{
case 0:
{
lean_object* v_key_2804_; uint8_t v___x_2805_; 
v_key_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_key_2804_);
lean_dec_ref_known(v___x_2803_, 2);
v___x_2805_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_2796_, v_key_2804_);
return v___x_2805_;
}
case 1:
{
lean_object* v_node_2806_; size_t v___x_2807_; 
v_node_2806_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_node_2806_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2807_ = lean_usize_shift_right(v_x_2795_, v___x_2799_);
v_x_2794_ = v_node_2806_;
v_x_2795_ = v___x_2807_;
goto _start;
}
default: 
{
uint8_t v___x_2809_; 
lean_dec_ref(v_x_2796_);
v___x_2809_ = 0;
return v___x_2809_;
}
}
}
else
{
lean_object* v_ks_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_ks_2810_ = lean_ctor_get(v_x_2794_, 0);
lean_inc_ref(v_ks_2810_);
lean_dec_ref_known(v_x_2794_, 2);
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_ks_2810_, v___x_2811_, v_x_2796_);
lean_dec_ref(v_ks_2810_);
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg___boxed(lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_){
_start:
{
size_t v_x_4073__boxed_2816_; uint8_t v_res_2817_; lean_object* v_r_2818_; 
v_x_4073__boxed_2816_ = lean_unbox_usize(v_x_2814_);
lean_dec(v_x_2814_);
v_res_2817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_2813_, v_x_4073__boxed_2816_, v_x_2815_);
v_r_2818_ = lean_box(v_res_2817_);
return v_r_2818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(lean_object* v_x_2819_, lean_object* v_x_2820_){
_start:
{
uint64_t v___y_2822_; lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_2820_);
if (lean_obj_tag(v___x_2825_) == 0)
{
uint64_t v___x_2826_; 
v___x_2826_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2822_ = v___x_2826_;
goto v___jp_2821_;
}
else
{
uint64_t v_hash_2827_; 
v_hash_2827_ = lean_ctor_get_uint64(v___x_2825_, sizeof(void*)*2);
lean_dec(v___x_2825_);
v___y_2822_ = v_hash_2827_;
goto v___jp_2821_;
}
v___jp_2821_:
{
size_t v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_uint64_to_usize(v___y_2822_);
v___x_2824_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_2819_, v___x_2823_, v_x_2820_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg___boxed(lean_object* v_x_2828_, lean_object* v_x_2829_){
_start:
{
uint8_t v_res_2830_; lean_object* v_r_2831_; 
v_res_2830_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_x_2828_, v_x_2829_);
v_r_2831_ = lean_box(v_res_2830_);
return v_r_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(lean_object* v_database_2832_, lean_object* v_as_2833_, size_t v_i_2834_, size_t v_stop_2835_, lean_object* v_b_2836_){
_start:
{
lean_object* v___y_2838_; uint8_t v___x_2842_; 
v___x_2842_ = lean_usize_dec_eq(v_i_2834_, v_stop_2835_);
if (v___x_2842_ == 0)
{
lean_object* v_erased_2843_; lean_object* v___x_2844_; lean_object* v_proof_2845_; uint8_t v___x_2846_; 
v_erased_2843_ = lean_ctor_get(v_database_2832_, 1);
v___x_2844_ = lean_array_uget_borrowed(v_as_2833_, v_i_2834_);
v_proof_2845_ = lean_ctor_get(v___x_2844_, 1);
lean_inc_ref(v_proof_2845_);
lean_inc_ref(v_erased_2843_);
v___x_2846_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_erased_2843_, v_proof_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; 
lean_inc(v___x_2844_);
v___x_2847_ = lean_array_push(v_b_2836_, v___x_2844_);
v___y_2838_ = v___x_2847_;
goto v___jp_2837_;
}
else
{
v___y_2838_ = v_b_2836_;
goto v___jp_2837_;
}
}
else
{
lean_dec_ref(v_database_2832_);
return v_b_2836_;
}
v___jp_2837_:
{
size_t v___x_2839_; size_t v___x_2840_; 
v___x_2839_ = ((size_t)1ULL);
v___x_2840_ = lean_usize_add(v_i_2834_, v___x_2839_);
v_i_2834_ = v___x_2840_;
v_b_2836_ = v___y_2838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3___boxed(lean_object* v_database_2848_, lean_object* v_as_2849_, lean_object* v_i_2850_, lean_object* v_stop_2851_, lean_object* v_b_2852_){
_start:
{
size_t v_i_boxed_2853_; size_t v_stop_boxed_2854_; lean_object* v_res_2855_; 
v_i_boxed_2853_ = lean_unbox_usize(v_i_2850_);
lean_dec(v_i_2850_);
v_stop_boxed_2854_ = lean_unbox_usize(v_stop_2851_);
lean_dec(v_stop_2851_);
v_res_2855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_2848_, v_as_2849_, v_i_boxed_2853_, v_stop_boxed_2854_, v_b_2852_);
lean_dec_ref(v_as_2849_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(lean_object* v_a_2859_, lean_object* v_as_2860_, size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_usize_dec_lt(v_i_2862_, v_sz_2861_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref(v_a_2859_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_b_2863_);
return v___x_2872_;
}
else
{
lean_object* v_a_2873_; lean_object* v_pattern_2874_; lean_object* v___x_2875_; 
lean_dec_ref(v_b_2863_);
v_a_2873_ = lean_array_uget_borrowed(v_as_2860_, v_i_2862_);
v_pattern_2874_ = lean_ctor_get(v_a_2873_, 0);
lean_inc_ref(v_a_2859_);
lean_inc_ref(v_pattern_2874_);
v___x_2875_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_2874_, v_a_2859_, v___x_2871_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2898_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2898_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2898_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_box(0);
if (lean_obj_tag(v_a_2876_) == 1)
{
lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2892_; 
lean_dec_ref(v_a_2859_);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_a_2876_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v_a_2876_, 0);
lean_dec(v_unused_2893_);
v___x_2882_ = v_a_2876_;
v_isShared_2883_ = v_isSharedCheck_2892_;
goto v_resetjp_2881_;
}
else
{
lean_dec(v_a_2876_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2892_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_inc(v_a_2873_);
v___x_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2873_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2884_);
v___x_2886_ = v___x_2882_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2880_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2887_);
v___x_2889_ = v___x_2878_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v___x_2894_; size_t v___x_2895_; size_t v___x_2896_; 
lean_del_object(v___x_2878_);
lean_dec(v_a_2876_);
v___x_2894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0));
v___x_2895_ = ((size_t)1ULL);
v___x_2896_ = lean_usize_add(v_i_2862_, v___x_2895_);
v_i_2862_ = v___x_2896_;
v_b_2863_ = v___x_2894_;
goto _start;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v_a_2859_);
v_a_2899_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2875_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2875_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___boxed(lean_object* v_a_2907_, lean_object* v_as_2908_, lean_object* v_sz_2909_, lean_object* v_i_2910_, lean_object* v_b_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
size_t v_sz_boxed_2919_; size_t v_i_boxed_2920_; lean_object* v_res_2921_; 
v_sz_boxed_2919_ = lean_unbox_usize(v_sz_2909_);
lean_dec(v_sz_2909_);
v_i_boxed_2920_ = lean_unbox_usize(v_i_2910_);
lean_dec(v_i_2910_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(v_a_2907_, v_as_2908_, v_sz_boxed_2919_, v_i_boxed_2920_, v_b_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec_ref(v_as_2908_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(lean_object* v_database_2922_, lean_object* v_e_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___x_2931_; lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_3004_; 
v___x_2931_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_2923_, v_a_2927_);
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_3004_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_3004_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2932_, v_a_2925_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2995_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2995_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2995_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_specs_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___y_2945_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_specs_2941_ = lean_ctor_get(v_database_2922_, 0);
v___x_2942_ = l_Lean_Meta_Sym_getMatch___redArg(v_specs_2941_, v_a_2937_);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_array_get_size(v___x_2942_);
v___x_2986_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0));
v___x_2987_ = lean_nat_dec_lt(v___x_2943_, v___x_2985_);
if (v___x_2987_ == 0)
{
lean_dec_ref(v___x_2942_);
lean_dec_ref(v_database_2922_);
v___y_2945_ = v___x_2986_;
goto v___jp_2944_;
}
else
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_nat_dec_le(v___x_2985_, v___x_2985_);
if (v___x_2988_ == 0)
{
if (v___x_2987_ == 0)
{
lean_dec_ref(v___x_2942_);
lean_dec_ref(v_database_2922_);
v___y_2945_ = v___x_2986_;
goto v___jp_2944_;
}
else
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_usize_of_nat(v___x_2985_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_2922_, v___x_2942_, v___x_2989_, v___x_2990_, v___x_2986_);
lean_dec_ref(v___x_2942_);
v___y_2945_ = v___x_2991_;
goto v___jp_2944_;
}
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = lean_usize_of_nat(v___x_2985_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_2922_, v___x_2942_, v___x_2992_, v___x_2993_, v___x_2986_);
lean_dec_ref(v___x_2942_);
v___y_2945_ = v___x_2994_;
goto v___jp_2944_;
}
}
v___jp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2946_ = lean_array_get_size(v___y_2945_);
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_dec_eq(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; size_t v_sz_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
lean_del_object(v___x_2939_);
v___x_2949_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v___y_2945_, v___x_2943_, v___x_2946_);
v___x_2950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0));
v_sz_2951_ = lean_array_size(v___x_2949_);
v___x_2952_ = ((size_t)0ULL);
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(v_a_2937_, v___x_2949_, v_sz_2951_, v___x_2952_, v___x_2950_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2969_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2969_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2969_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_fst_2958_; 
v_fst_2958_ = lean_ctor_get(v_a_2954_, 0);
lean_inc(v_fst_2958_);
lean_dec(v_a_2954_);
if (lean_obj_tag(v_fst_2958_) == 0)
{
lean_object* v___x_2960_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2949_);
v___x_2960_ = v___x_2934_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2949_);
v___x_2960_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2962_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2960_);
v___x_2962_ = v___x_2956_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_object* v_val_2965_; lean_object* v___x_2967_; 
lean_dec_ref(v___x_2949_);
lean_del_object(v___x_2934_);
v_val_2965_ = lean_ctor_get(v_fst_2958_, 0);
lean_inc(v_val_2965_);
lean_dec_ref_known(v_fst_2958_, 1);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v_val_2965_);
v___x_2967_ = v___x_2956_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_val_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v___x_2949_);
lean_del_object(v___x_2934_);
v_a_2970_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2953_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2953_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_dec(v_a_2937_);
v___x_2978_ = lean_array_fget(v___y_2945_, v___x_2943_);
lean_dec_ref(v___y_2945_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 1);
lean_ctor_set(v___x_2934_, 0, v___x_2978_);
v___x_2980_ = v___x_2934_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2982_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2980_);
v___x_2982_ = v___x_2939_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_del_object(v___x_2934_);
lean_dec_ref(v_database_2922_);
v_a_2996_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2936_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2936_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(lean_object* v_database_3005_, lean_object* v_e_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(v_database_3005_, v_e_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3014_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(lean_object* v_00_u03b2_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_x_3016_, v_x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___boxed(lean_object* v_00_u03b2_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(v_00_u03b2_3019_, v_x_3020_, v_x_3021_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(lean_object* v_00_u03b2_3024_, lean_object* v_x_3025_, size_t v_x_3026_, lean_object* v_x_3027_){
_start:
{
uint8_t v___x_3028_; 
v___x_3028_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_3025_, v_x_3026_, v_x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3029_, lean_object* v_x_3030_, lean_object* v_x_3031_, lean_object* v_x_3032_){
_start:
{
size_t v_x_4418__boxed_3033_; uint8_t v_res_3034_; lean_object* v_r_3035_; 
v_x_4418__boxed_3033_ = lean_unbox_usize(v_x_3031_);
lean_dec(v_x_3031_);
v_res_3034_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(v_00_u03b2_3029_, v_x_3030_, v_x_4418__boxed_3033_, v_x_3032_);
v_r_3035_ = lean_box(v_res_3034_);
return v_r_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2(lean_object* v_xs_3036_, lean_object* v_j_3037_, lean_object* v_h_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(v_xs_3036_, v_j_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3040_, lean_object* v_keys_3041_, lean_object* v_vals_3042_, lean_object* v_heq_3043_, lean_object* v_i_3044_, lean_object* v_k_3045_){
_start:
{
uint8_t v___x_3046_; 
v___x_3046_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_keys_3041_, v_i_3044_, v_k_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3047_, lean_object* v_keys_3048_, lean_object* v_vals_3049_, lean_object* v_heq_3050_, lean_object* v_i_3051_, lean_object* v_k_3052_){
_start:
{
uint8_t v_res_3053_; lean_object* v_r_3054_; 
v_res_3053_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(v_00_u03b2_3047_, v_keys_3048_, v_vals_3049_, v_heq_3050_, v_i_3051_, v_k_3052_);
lean_dec_ref(v_vals_3049_);
lean_dec_ref(v_keys_3048_);
v_r_3054_ = lean_box(v_res_3053_);
return v_r_3054_;
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
