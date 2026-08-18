// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.CbvSimproc
// Imports: public import Lean.Compiler.InitAttr public import Lean.ScopedEnvExtension public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Simp.Result public import Lean.Meta.Sym.Simp.App public import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Meta.Sym.Pattern
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_initializing();
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Tactic.Cbv.CbvSimprocPhase.pre"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Cbv.CbvSimprocPhase.eval"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Cbv.CbvSimprocPhase.post"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CbvSimprocPhase"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(174, 198, 190, 17, 0, 62, 186, 92)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(136, 145, 164, 233, 233, 175, 160, 110)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "post"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(119, 117, 11, 53, 165, 217, 228, 6)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase;
static const lean_array_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs;
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "Invalid builtin cbv simproc declaration: It can only be registered during initialization"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid builtin cbv simproc declaration `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`: It has already been declared"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbvSimprocDeclExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 182, 205, 129, 188, 54, 74, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Invalid cbv simproc declaration `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: It is declared in an imported module"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Cbv simproc `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "` has an unexpected type: Expected `Simproc`, but found `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cbvSimprocExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 184, 164, 42, 54, 246, 220, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not have a [cbv_simproc] attribute"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Invalid `[cbv_simproc]` attribute: `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a cbv simproc"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocEval"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 221, 189, 14, 79, 87, 225, 132)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocAttr"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 104, 242, 136, 13, 73, 193, 222)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Invalid `[builtin_cbv_simproc]` attribute: `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` is not a builtin cbv simproc"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "addCbvSimprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 46, 19, 141, 119, 105, 81, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CbvSimproc"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 246, 233, 32, 144, 0, 48, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(111, 195, 33, 67, 227, 201, 233, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 80, 153, 5, 12, 193, 47, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 121, 100, 52, 100, 248, 58, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 62, 250, 213, 135, 222, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(213, 6, 85, 205, 253, 185, 83, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 49, 121, 44, 210, 159, 116, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 89, 200, 112, 232, 34, 102, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 228, 129, 159, 189, 107, 203, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 188, 21, 86, 205, 70, 6, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 176, 116, 134, 116, 89, 199, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(31, 64, 46, 173, 247, 116, 204, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 173, 236, 92, 177, 72, 11, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)(((size_t)(735115364) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(127, 15, 195, 174, 145, 172, 96, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(20, 75, 147, 248, 238, 192, 151, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 247, 227, 4, 148, 191, 156, 205)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(113, 151, 92, 207, 210, 188, 39, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Cbv simplification procedure"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Not implemented yet, [-builtin_cbv_simproc]"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cbvSimprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 176, 240, 9, 13, 93, 32, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Builtin cbv simplification procedure"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simproc "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ": done"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": no change"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simprocs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 69, 90, 123, 228, 205, 71, 22)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(lean_object* v_pre_23_){
_start:
{
lean_inc(v_pre_23_);
return v_pre_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(lean_object* v_pre_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(v_pre_24_);
lean_dec(v_pre_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_pre_29_){
_start:
{
lean_inc(v_pre_29_);
return v_pre_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_pre_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_pre_33_);
lean_dec(v_pre_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(lean_object* v_eval_36_){
_start:
{
lean_inc(v_eval_36_);
return v_eval_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(lean_object* v_eval_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(v_eval_37_);
lean_dec(v_eval_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_eval_42_){
_start:
{
lean_inc(v_eval_42_);
return v_eval_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_eval_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_eval_46_);
lean_dec(v_eval_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(lean_object* v_post_49_){
_start:
{
lean_inc(v_post_49_);
return v_post_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(lean_object* v_post_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(v_post_50_);
lean_dec(v_post_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_post_55_){
_start:
{
lean_inc(v_post_55_);
return v_post_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_post_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_post_59_);
lean_dec(v_post_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_17__boxed_71_; uint8_t v_y_18__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_17__boxed_71_ = lean_unbox(v_x_69_);
v_y_18__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(v_x_17__boxed_71_, v_y_18__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(uint8_t v_x_77_){
_start:
{
switch(v_x_77_)
{
case 0:
{
uint64_t v___x_78_; 
v___x_78_ = 0ULL;
return v___x_78_;
}
case 1:
{
uint64_t v___x_79_; 
v___x_79_ = 1ULL;
return v___x_79_;
}
default: 
{
uint64_t v___x_80_; 
v___x_80_ = 2ULL;
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(lean_object* v_x_81_){
_start:
{
uint8_t v_x_40__boxed_82_; uint64_t v_res_83_; lean_object* v_r_84_; 
v_x_40__boxed_82_ = lean_unbox(v_x_81_);
v_res_83_ = l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(v_x_40__boxed_82_);
v_r_84_ = lean_box_uint64(v_res_83_);
return v_r_84_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(2u);
v___x_97_ = lean_nat_to_int(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_to_int(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(uint8_t v_x_100_, lean_object* v_prec_101_){
_start:
{
lean_object* v___y_103_; lean_object* v___y_110_; lean_object* v___y_117_; 
switch(v_x_100_)
{
case 0:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1024u);
v___x_124_ = lean_nat_dec_le(v___x_123_, v_prec_101_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_103_ = v___x_125_;
goto v___jp_102_;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_103_ = v___x_126_;
goto v___jp_102_;
}
}
case 1:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_101_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_110_ = v___x_129_;
goto v___jp_109_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_110_ = v___x_130_;
goto v___jp_109_;
}
}
default: 
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_101_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_117_ = v___x_133_;
goto v___jp_116_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_117_ = v___x_134_;
goto v___jp_116_;
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1));
lean_inc(v___y_103_);
v___x_105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_105_, 0, v___y_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_106_);
v___x_108_ = l_Repr_addAppParen(v___x_107_, v_prec_101_);
return v___x_108_;
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3));
lean_inc(v___y_110_);
v___x_112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_112_, 0, v___y_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_113_);
v___x_115_ = l_Repr_addAppParen(v___x_114_, v_prec_101_);
return v___x_115_;
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5));
lean_inc(v___y_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___y_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = l_Repr_addAppParen(v___x_121_, v_prec_101_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(lean_object* v_x_135_, lean_object* v_prec_136_){
_start:
{
uint8_t v_x_177__boxed_137_; lean_object* v_res_138_; 
v_x_177__boxed_137_ = lean_unbox(v_x_135_);
v_res_138_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(v_x_177__boxed_137_, v_prec_136_);
lean_dec(v_prec_136_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6));
v___x_156_ = l_Lean_mkConst(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9));
v___x_167_ = l_Lean_mkConst(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_box(0);
v___x_177_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12));
v___x_178_ = l_Lean_mkConst(v___x_177_, v___x_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(uint8_t v_x_179_){
_start:
{
switch(v_x_179_)
{
case 0:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
return v___x_180_;
}
case 1:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
return v___x_181_;
}
default: 
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(lean_object* v_x_183_){
_start:
{
uint8_t v_x_196__boxed_184_; lean_object* v_res_185_; 
v_x_196__boxed_184_ = lean_unbox(v_x_183_);
v_res_185_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(v_x_196__boxed_184_);
return v_res_185_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1));
v___x_195_ = l_Lean_mkConst(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2);
v___f_197_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0));
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___f_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3);
return v___x_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(lean_object* v_e_u2081_208_, lean_object* v_e_u2082_209_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_210_; lean_object* v_toCbvSimprocOLeanEntry_211_; lean_object* v_declName_212_; lean_object* v_declName_213_; uint8_t v___x_214_; 
v_toCbvSimprocOLeanEntry_210_ = lean_ctor_get(v_e_u2081_208_, 0);
v_toCbvSimprocOLeanEntry_211_ = lean_ctor_get(v_e_u2082_209_, 0);
v_declName_212_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_210_, 0);
v_declName_213_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_211_, 0);
v___x_214_ = lean_name_eq(v_declName_212_, v_declName_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(lean_object* v_e_u2081_215_, lean_object* v_e_u2082_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(v_e_u2081_215_, v_e_u2082_216_);
lean_dec_ref(v_e_u2082_216_);
lean_dec_ref(v_e_u2081_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(lean_object* v_e_221_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_222_; lean_object* v_declName_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_toCbvSimprocOLeanEntry_222_ = lean_ctor_get(v_e_221_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_222_);
lean_dec_ref(v_e_221_);
v_declName_223_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_222_, 0);
lean_inc(v_declName_223_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_222_);
v___x_224_ = 1;
v___x_225_ = l_Lean_Name_toString(v_declName_223_, v___x_224_);
v___x_226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_229_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object* v_00_u03b2_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_box(0));
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2);
v___x_239_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1);
v___x_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
lean_ctor_set(v___x_240_, 3, v___x_238_);
lean_ctor_set(v___x_240_, 4, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(lean_object* v_xs_243_, lean_object* v_v_244_, lean_object* v_i_245_){
_start:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_array_get_size(v_xs_243_);
v___x_247_ = lean_nat_dec_lt(v_i_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_i_245_);
v___x_248_ = lean_box(0);
return v___x_248_;
}
else
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_fget_borrowed(v_xs_243_, v_i_245_);
v___x_250_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_249_, v_v_244_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_add(v_i_245_, v___x_251_);
lean_dec(v_i_245_);
v_i_245_ = v___x_252_;
goto _start;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_i_245_);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17___boxed(lean_object* v_xs_255_, lean_object* v_v_256_, lean_object* v_i_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(v_xs_255_, v_v_256_, v_i_257_);
lean_dec(v_v_256_);
lean_dec_ref(v_xs_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(lean_object* v_xs_259_, lean_object* v_v_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(v_xs_259_, v_v_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11___boxed(lean_object* v_xs_263_, lean_object* v_v_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(v_xs_263_, v_v_264_);
lean_dec(v_v_264_);
lean_dec_ref(v_xs_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(lean_object* v_x_266_, lean_object* v_keys_267_, lean_object* v_v_268_, lean_object* v_k_269_, lean_object* v_x_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_c_273_; lean_object* v___x_274_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_x_266_, v___x_271_);
v_c_273_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_267_, v_v_268_, v___x_272_);
lean_dec(v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_k_269_);
lean_ctor_set(v___x_274_, 1, v_c_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_x_275_, lean_object* v_keys_276_, lean_object* v_v_277_, lean_object* v_k_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_275_, v_keys_276_, v_v_277_, v_k_278_, v_x_279_);
lean_dec_ref(v_keys_276_);
lean_dec(v_x_275_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_fst_283_; lean_object* v_fst_284_; uint8_t v___x_285_; 
v_fst_283_ = lean_ctor_get(v_a_281_, 0);
v_fst_284_ = lean_ctor_get(v_b_282_, 0);
v___x_285_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_283_, v_fst_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1___boxed(lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_a_286_, v_b_287_);
lean_dec_ref(v_b_287_);
lean_dec_ref(v_a_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object* v_vs_290_, lean_object* v_v_291_, lean_object* v_i_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_array_get_size(v_vs_290_);
v___x_294_ = lean_nat_dec_lt(v_i_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec(v_i_292_);
v___x_295_ = lean_array_push(v_vs_290_, v_v_291_);
return v___x_295_;
}
else
{
lean_object* v_toCbvSimprocOLeanEntry_296_; lean_object* v_declName_297_; lean_object* v___x_298_; lean_object* v_toCbvSimprocOLeanEntry_299_; lean_object* v_declName_300_; uint8_t v___x_301_; 
v_toCbvSimprocOLeanEntry_296_ = lean_ctor_get(v_v_291_, 0);
v_declName_297_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_296_, 0);
v___x_298_ = lean_array_fget_borrowed(v_vs_290_, v_i_292_);
v_toCbvSimprocOLeanEntry_299_ = lean_ctor_get(v___x_298_, 0);
v_declName_300_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_299_, 0);
v___x_301_ = lean_name_eq(v_declName_297_, v_declName_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_i_292_, v___x_302_);
lean_dec(v_i_292_);
v_i_292_ = v___x_303_;
goto _start;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_array_fset(v_vs_290_, v_i_292_, v_v_291_);
lean_dec(v_i_292_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object* v_vs_306_, lean_object* v_v_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(v_vs_306_, v_v_307_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(lean_object* v_x_314_, lean_object* v_keys_315_, lean_object* v_v_316_, lean_object* v_k_317_, lean_object* v_as_318_, lean_object* v_k_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_mid_324_; lean_object* v_midVal_325_; uint8_t v___x_326_; 
v___x_322_ = lean_nat_add(v_x_320_, v_x_321_);
v___x_323_ = lean_unsigned_to_nat(1u);
v_mid_324_ = lean_nat_shiftr(v___x_322_, v___x_323_);
lean_dec(v___x_322_);
v_midVal_325_ = lean_array_fget(v_as_318_, v_mid_324_);
v___x_326_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_midVal_325_, v_k_319_);
if (v___x_326_ == 0)
{
uint8_t v___x_327_; 
lean_dec(v_x_321_);
v___x_327_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_319_, v_midVal_325_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
lean_dec(v_x_320_);
v___x_328_ = lean_array_get_size(v_as_318_);
v___x_329_ = lean_nat_dec_lt(v_mid_324_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec(v_midVal_325_);
lean_dec(v_mid_324_);
lean_dec(v_k_317_);
lean_dec_ref(v_v_316_);
return v_as_318_;
}
else
{
lean_object* v_snd_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_342_; 
v_snd_330_ = lean_ctor_get(v_midVal_325_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_midVal_325_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v_midVal_325_, 0);
lean_dec(v_unused_343_);
v___x_332_ = v_midVal_325_;
v_isShared_333_ = v_isSharedCheck_342_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_snd_330_);
lean_dec(v_midVal_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_342_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v_xs_x27_335_; lean_object* v___x_336_; lean_object* v_c_337_; lean_object* v___x_339_; 
v___x_334_ = lean_box(0);
v_xs_x27_335_ = lean_array_fset(v_as_318_, v_mid_324_, v___x_334_);
v___x_336_ = lean_nat_add(v_x_314_, v___x_323_);
v_c_337_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_315_, v_v_316_, v___x_336_, v_snd_330_);
lean_dec(v___x_336_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_c_337_);
lean_ctor_set(v___x_332_, 0, v_k_317_);
v___x_339_ = v___x_332_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_c_337_);
v___x_339_ = v_reuseFailAlloc_341_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_fset(v_xs_x27_335_, v_mid_324_, v___x_339_);
lean_dec(v_mid_324_);
return v___x_340_;
}
}
}
}
else
{
lean_dec(v_midVal_325_);
v_x_321_ = v_mid_324_;
goto _start;
}
}
else
{
uint8_t v___x_345_; 
lean_dec(v_midVal_325_);
v___x_345_ = lean_nat_dec_eq(v_mid_324_, v_x_320_);
if (v___x_345_ == 0)
{
lean_dec(v_x_320_);
v_x_320_ = v_mid_324_;
goto _start;
}
else
{
lean_object* v___x_347_; lean_object* v_c_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_j_351_; lean_object* v_as_352_; lean_object* v___x_353_; 
lean_dec(v_mid_324_);
lean_dec(v_x_321_);
v___x_347_ = lean_nat_add(v_x_314_, v___x_323_);
v_c_348_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_315_, v_v_316_, v___x_347_);
lean_dec(v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_k_317_);
lean_ctor_set(v___x_349_, 1, v_c_348_);
v___x_350_ = lean_nat_add(v_x_320_, v___x_323_);
lean_dec(v_x_320_);
v_j_351_ = lean_array_get_size(v_as_318_);
v_as_352_ = lean_array_push(v_as_318_, v___x_349_);
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_350_, v_as_352_, v_j_351_);
lean_dec(v___x_350_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(lean_object* v_x_354_, lean_object* v_keys_355_, lean_object* v_v_356_, lean_object* v_k_357_, lean_object* v_as_358_, lean_object* v_k_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_array_get_size(v_as_358_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_array_fget_borrowed(v_as_358_, v___x_361_);
v___x_364_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_359_, v___x_363_);
if (v___x_364_ == 0)
{
uint8_t v___x_365_; 
v___x_365_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v___x_363_, v_k_359_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_lt(v___x_361_, v___x_360_);
if (v___x_366_ == 0)
{
lean_dec(v_k_357_);
lean_dec_ref(v_v_356_);
return v_as_358_;
}
else
{
lean_object* v___x_367_; lean_object* v_xs_x27_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
lean_inc(v___x_363_);
v___x_367_ = lean_box(0);
v_xs_x27_368_ = lean_array_fset(v_as_358_, v___x_361_, v___x_367_);
v___x_369_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v___x_363_);
v___x_370_ = lean_array_fset(v_xs_x27_368_, v___x_361_, v___x_369_);
return v___x_370_;
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_sub(v___x_360_, v___x_371_);
v___x_373_ = lean_array_fget_borrowed(v_as_358_, v___x_372_);
v___x_374_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v___x_373_, v_k_359_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_359_, v___x_373_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_lt(v___x_372_, v___x_360_);
if (v___x_376_ == 0)
{
lean_dec(v___x_372_);
lean_dec(v_k_357_);
lean_dec_ref(v_v_356_);
return v_as_358_;
}
else
{
lean_object* v___x_377_; lean_object* v_xs_x27_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
lean_inc(v___x_373_);
v___x_377_ = lean_box(0);
v_xs_x27_378_ = lean_array_fset(v_as_358_, v___x_372_, v___x_377_);
v___x_379_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v___x_373_);
v___x_380_ = lean_array_fset(v_xs_x27_378_, v___x_372_, v___x_379_);
lean_dec(v___x_372_);
return v___x_380_;
}
}
else
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v_as_358_, v_k_359_, v___x_361_, v___x_372_);
return v___x_381_;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v___x_372_);
v___x_382_ = lean_box(0);
v___x_383_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v___x_382_);
v___x_384_ = lean_array_push(v_as_358_, v___x_383_);
return v___x_384_;
}
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_as_387_; lean_object* v___x_388_; 
v___x_385_ = lean_box(0);
v___x_386_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v___x_385_);
v_as_387_ = lean_array_push(v_as_358_, v___x_386_);
v___x_388_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_361_, v_as_387_, v___x_360_);
return v___x_388_;
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_box(0);
v___x_390_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_354_, v_keys_355_, v_v_356_, v_k_357_, v___x_389_);
v___x_391_ = lean_array_push(v_as_358_, v___x_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object* v_keys_392_, lean_object* v_v_393_, lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
lean_object* v_vs_396_; lean_object* v_children_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_414_; 
v_vs_396_ = lean_ctor_get(v_x_395_, 0);
v_children_397_ = lean_ctor_get(v_x_395_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_395_);
if (v_isSharedCheck_414_ == 0)
{
v___x_399_ = v_x_395_;
v_isShared_400_ = v_isSharedCheck_414_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_children_397_);
lean_inc(v_vs_396_);
lean_dec(v_x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_414_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_array_get_size(v_keys_392_);
v___x_402_ = lean_nat_dec_lt(v_x_394_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v_vs_396_, v_v_393_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_403_);
v___x_405_ = v___x_399_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_children_397_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v_k_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_c_410_; lean_object* v___x_412_; 
v_k_407_ = lean_array_fget_borrowed(v_keys_392_, v_x_394_);
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1));
lean_inc_n(v_k_407_, 2);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_k_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v_c_410_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_x_394_, v_keys_392_, v_v_393_, v_k_407_, v_children_397_, v___x_409_);
lean_dec_ref_known(v___x_409_, 2);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v_c_410_);
v___x_412_ = v___x_399_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_vs_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_c_410_);
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
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(lean_object* v_x_415_, lean_object* v_keys_416_, lean_object* v_v_417_, lean_object* v_k_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_snd_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
v_snd_420_ = lean_ctor_get(v_x_419_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_x_419_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v_x_419_, 0);
lean_dec(v_unused_431_);
v___x_422_ = v_x_419_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_snd_420_);
lean_dec(v_x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_c_426_; lean_object* v___x_428_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_x_415_, v___x_424_);
v_c_426_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_416_, v_v_417_, v___x_425_, v_snd_420_);
lean_dec(v___x_425_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v_c_426_);
lean_ctor_set(v___x_422_, 0, v_k_418_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_k_418_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_c_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2___boxed(lean_object* v_x_432_, lean_object* v_keys_433_, lean_object* v_v_434_, lean_object* v_k_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_432_, v_keys_433_, v_v_434_, v_k_435_, v_x_436_);
lean_dec_ref(v_keys_433_);
lean_dec(v_x_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object* v_keys_438_, lean_object* v_v_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_438_, v_v_439_, v_x_440_, v_x_441_);
lean_dec(v_x_440_);
lean_dec_ref(v_keys_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object* v_x_443_, lean_object* v_keys_444_, lean_object* v_v_445_, lean_object* v_k_446_, lean_object* v_as_447_, lean_object* v_k_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_443_, v_keys_444_, v_v_445_, v_k_446_, v_as_447_, v_k_448_, v_x_449_, v_x_450_);
lean_dec_ref(v_k_448_);
lean_dec_ref(v_keys_444_);
lean_dec(v_x_443_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___boxed(lean_object* v_x_452_, lean_object* v_keys_453_, lean_object* v_v_454_, lean_object* v_k_455_, lean_object* v_as_456_, lean_object* v_k_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_x_452_, v_keys_453_, v_v_454_, v_k_455_, v_as_456_, v_k_457_);
lean_dec_ref(v_k_457_);
lean_dec_ref(v_keys_453_);
lean_dec(v_x_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(lean_object* v_keys_459_, lean_object* v_v_460_, lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_459_, v_v_460_, v___x_462_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
else
{
lean_object* v_val_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_val_465_ = lean_ctor_get(v_x_461_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_461_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v_x_461_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_val_465_);
lean_dec(v_x_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_459_, v_v_460_, v___x_469_, v_val_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0___boxed(lean_object* v_keys_475_, lean_object* v_v_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_475_, v_v_476_, v_x_477_);
lean_dec_ref(v_keys_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_ks_483_; lean_object* v_vs_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_508_; 
v_ks_483_ = lean_ctor_get(v_x_479_, 0);
v_vs_484_ = lean_ctor_get(v_x_479_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_508_ == 0)
{
v___x_486_ = v_x_479_;
v_isShared_487_ = v_isSharedCheck_508_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_vs_484_);
lean_inc(v_ks_483_);
lean_dec(v_x_479_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_508_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_array_get_size(v_ks_483_);
v___x_489_ = lean_nat_dec_lt(v_x_480_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_x_480_);
v___x_490_ = lean_array_push(v_ks_483_, v_x_481_);
v___x_491_ = lean_array_push(v_vs_484_, v_x_482_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_491_);
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_493_ = v___x_486_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v_k_x27_495_; uint8_t v___x_496_; 
v_k_x27_495_ = lean_array_fget_borrowed(v_ks_483_, v_x_480_);
v___x_496_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_481_, v_k_x27_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_498_; 
if (v_isShared_487_ == 0)
{
v___x_498_ = v___x_486_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_ks_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_vs_484_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_x_480_, v___x_499_);
lean_dec(v_x_480_);
v_x_479_ = v___x_498_;
v_x_480_ = v___x_500_;
goto _start;
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_503_ = lean_array_fset(v_ks_483_, v_x_480_, v_x_481_);
v___x_504_ = lean_array_fset(v_vs_484_, v_x_480_, v_x_482_);
lean_dec(v_x_480_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_504_);
lean_ctor_set(v___x_486_, 0, v___x_503_);
v___x_506_ = v___x_486_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(lean_object* v_n_509_, lean_object* v_k_510_, lean_object* v_v_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(v_n_509_, v___x_512_, v_k_510_, v_v_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(lean_object* v_x_515_, size_t v_x_516_, size_t v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v_es_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_j_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_es_520_ = lean_ctor_get(v_x_515_, 0);
v___x_521_ = ((size_t)31ULL);
v___x_522_ = lean_usize_land(v_x_516_, v___x_521_);
v_j_523_ = lean_usize_to_nat(v___x_522_);
v___x_524_ = lean_array_get_size(v_es_520_);
v___x_525_ = lean_nat_dec_lt(v_j_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v_j_523_);
lean_dec(v_x_519_);
lean_dec(v_x_518_);
return v_x_515_;
}
else
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_564_; 
lean_inc_ref(v_es_520_);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_x_515_, 0);
lean_dec(v_unused_565_);
v___x_527_ = v_x_515_;
v_isShared_528_ = v_isSharedCheck_564_;
goto v_resetjp_526_;
}
else
{
lean_dec(v_x_515_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_564_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_v_529_; lean_object* v___x_530_; lean_object* v_xs_x27_531_; lean_object* v___y_533_; 
v_v_529_ = lean_array_fget(v_es_520_, v_j_523_);
v___x_530_ = lean_box(0);
v_xs_x27_531_ = lean_array_fset(v_es_520_, v_j_523_, v___x_530_);
switch(lean_obj_tag(v_v_529_))
{
case 0:
{
lean_object* v_key_538_; lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_549_; 
v_key_538_ = lean_ctor_get(v_v_529_, 0);
v_val_539_ = lean_ctor_get(v_v_529_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_v_529_);
if (v_isSharedCheck_549_ == 0)
{
v___x_541_ = v_v_529_;
v_isShared_542_ = v_isSharedCheck_549_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_inc(v_key_538_);
lean_dec(v_v_529_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_549_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_518_, v_key_538_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_del_object(v___x_541_);
v___x_544_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_538_, v_val_539_, v_x_518_, v_x_519_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___y_533_ = v___x_545_;
goto v___jp_532_;
}
else
{
lean_object* v___x_547_; 
lean_dec(v_val_539_);
lean_dec(v_key_538_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_x_519_);
lean_ctor_set(v___x_541_, 0, v_x_518_);
v___x_547_ = v___x_541_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_x_518_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_x_519_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
v___y_533_ = v___x_547_;
goto v___jp_532_;
}
}
}
}
case 1:
{
lean_object* v_node_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_562_; 
v_node_550_ = lean_ctor_get(v_v_529_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_v_529_);
if (v_isSharedCheck_562_ == 0)
{
v___x_552_ = v_v_529_;
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_node_550_);
lean_dec(v_v_529_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_554_ = ((size_t)5ULL);
v___x_555_ = lean_usize_shift_right(v_x_516_, v___x_554_);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_x_517_, v___x_556_);
v___x_558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_node_550_, v___x_555_, v___x_557_, v_x_518_, v_x_519_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_558_);
v___x_560_ = v___x_552_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v___y_533_ = v___x_560_;
goto v___jp_532_;
}
}
}
default: 
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_x_518_);
lean_ctor_set(v___x_563_, 1, v_x_519_);
v___y_533_ = v___x_563_;
goto v___jp_532_;
}
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_array_fset(v_xs_x27_531_, v_j_523_, v___y_533_);
lean_dec(v_j_523_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_534_);
v___x_536_ = v___x_527_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v_ks_566_; lean_object* v_vs_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_587_; 
v_ks_566_ = lean_ctor_get(v_x_515_, 0);
v_vs_567_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_587_ == 0)
{
v___x_569_ = v_x_515_;
v_isShared_570_ = v_isSharedCheck_587_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_vs_567_);
lean_inc(v_ks_566_);
lean_dec(v_x_515_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_587_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_ks_566_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_vs_567_);
v___x_572_ = v_reuseFailAlloc_586_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v_newNode_573_; uint8_t v___y_575_; size_t v___x_581_; uint8_t v___x_582_; 
v_newNode_573_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(v___x_572_, v_x_518_, v_x_519_);
v___x_581_ = ((size_t)7ULL);
v___x_582_ = lean_usize_dec_le(v___x_581_, v_x_517_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_573_);
v___x_584_ = lean_unsigned_to_nat(4u);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
lean_dec(v___x_583_);
v___y_575_ = v___x_585_;
goto v___jp_574_;
}
else
{
v___y_575_ = v___x_582_;
goto v___jp_574_;
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
lean_object* v_ks_576_; lean_object* v_vs_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_ks_576_ = lean_ctor_get(v_newNode_573_, 0);
lean_inc_ref(v_ks_576_);
v_vs_577_ = lean_ctor_get(v_newNode_573_, 1);
lean_inc_ref(v_vs_577_);
lean_dec_ref(v_newNode_573_);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0);
v___x_580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_x_517_, v_ks_576_, v_vs_577_, v___x_578_, v___x_579_);
lean_dec_ref(v_vs_577_);
lean_dec_ref(v_ks_576_);
return v___x_580_;
}
else
{
return v_newNode_573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(size_t v_depth_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_i_591_, lean_object* v_entries_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_keys_589_);
v___x_594_ = lean_nat_dec_lt(v_i_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_i_591_);
return v_entries_592_;
}
else
{
lean_object* v_k_595_; lean_object* v_v_596_; uint64_t v___x_597_; size_t v_h_598_; size_t v___x_599_; lean_object* v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v_h_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_k_595_ = lean_array_fget_borrowed(v_keys_589_, v_i_591_);
v_v_596_ = lean_array_fget_borrowed(v_vals_590_, v_i_591_);
v___x_597_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_595_);
v_h_598_ = lean_uint64_to_usize(v___x_597_);
v___x_599_ = ((size_t)5ULL);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_sub(v_depth_588_, v___x_601_);
v___x_603_ = lean_usize_mul(v___x_599_, v___x_602_);
v_h_604_ = lean_usize_shift_right(v_h_598_, v___x_603_);
v___x_605_ = lean_nat_add(v_i_591_, v___x_600_);
lean_dec(v_i_591_);
lean_inc(v_v_596_);
lean_inc(v_k_595_);
v___x_606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_entries_592_, v_h_604_, v_depth_588_, v_k_595_, v_v_596_);
v_i_591_ = v___x_605_;
v_entries_592_ = v___x_606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg___boxed(lean_object* v_depth_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_i_611_, lean_object* v_entries_612_){
_start:
{
size_t v_depth_boxed_613_; lean_object* v_res_614_; 
v_depth_boxed_613_ = lean_unbox_usize(v_depth_608_);
lean_dec(v_depth_608_);
v_res_614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_depth_boxed_613_, v_keys_609_, v_vals_610_, v_i_611_, v_entries_612_);
lean_dec_ref(v_vals_610_);
lean_dec_ref(v_keys_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
size_t v_x_2404__boxed_620_; size_t v_x_2405__boxed_621_; lean_object* v_res_622_; 
v_x_2404__boxed_620_ = lean_unbox_usize(v_x_616_);
lean_dec(v_x_616_);
v_x_2405__boxed_621_ = lean_unbox_usize(v_x_617_);
lean_dec(v_x_617_);
v_res_622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_x_615_, v_x_2404__boxed_620_, v_x_2405__boxed_621_, v_x_618_, v_x_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object* v_keys_623_, lean_object* v_v_624_, lean_object* v_x_625_, size_t v_x_626_, size_t v_x_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
lean_object* v_es_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v_j_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_es_629_ = lean_ctor_get(v_x_625_, 0);
v___x_630_ = ((size_t)31ULL);
v___x_631_ = lean_usize_land(v_x_626_, v___x_630_);
v_j_632_ = lean_usize_to_nat(v___x_631_);
v___x_633_ = lean_array_get_size(v_es_629_);
v___x_634_ = lean_nat_dec_lt(v_j_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec(v_j_632_);
lean_dec(v_x_628_);
lean_dec_ref(v_v_624_);
return v_x_625_;
}
else
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_702_; 
lean_inc_ref(v_es_629_);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_x_625_, 0);
lean_dec(v_unused_703_);
v___x_636_ = v_x_625_;
v_isShared_637_ = v_isSharedCheck_702_;
goto v_resetjp_635_;
}
else
{
lean_dec(v_x_625_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_702_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_v_638_; lean_object* v___x_639_; lean_object* v_xs_x27_640_; lean_object* v___y_642_; 
v_v_638_ = lean_array_fget(v_es_629_, v_j_632_);
v___x_639_ = lean_box(0);
v_xs_x27_640_ = lean_array_fset(v_es_629_, v_j_632_, v___x_639_);
switch(lean_obj_tag(v_v_638_))
{
case 0:
{
lean_object* v_key_647_; lean_object* v_val_648_; uint8_t v___x_649_; 
v_key_647_ = lean_ctor_get(v_v_638_, 0);
v_val_648_ = lean_ctor_get(v_v_638_, 1);
v___x_649_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_628_, v_key_647_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_623_, v_v_624_, v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_dec(v_x_628_);
v___y_642_ = v_v_638_;
goto v___jp_641_;
}
else
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
lean_inc(v_val_648_);
lean_inc(v_key_647_);
lean_dec_ref_known(v_v_638_, 2);
v_val_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_647_, v_val_648_, v_x_628_, v_val_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v___y_642_ = v___x_658_;
goto v___jp_641_;
}
}
}
}
else
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_671_; 
lean_inc(v_val_648_);
v_isSharedCheck_671_ = !lean_is_exclusive(v_v_638_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; 
v_unused_672_ = lean_ctor_get(v_v_638_, 1);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_v_638_, 0);
lean_dec(v_unused_673_);
v___x_662_ = v_v_638_;
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_v_638_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_val_648_);
v___x_665_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_623_, v_v_624_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
lean_del_object(v___x_662_);
lean_dec(v_x_628_);
v___x_666_ = lean_box(2);
v___y_642_ = v___x_666_;
goto v___jp_641_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; 
v_val_667_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v___x_665_, 1);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v_val_667_);
lean_ctor_set(v___x_662_, 0, v_x_628_);
v___x_669_ = v___x_662_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_x_628_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_val_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
v___y_642_ = v___x_669_;
goto v___jp_641_;
}
}
}
}
}
case 1:
{
lean_object* v_node_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_697_; 
v_node_674_ = lean_ctor_get(v_v_638_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v_v_638_);
if (v_isSharedCheck_697_ == 0)
{
v___x_676_ = v_v_638_;
v_isShared_677_ = v_isSharedCheck_697_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_node_674_);
lean_dec(v_v_638_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_697_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v_newNode_682_; lean_object* v___x_683_; 
v___x_678_ = ((size_t)5ULL);
v___x_679_ = lean_usize_shift_right(v_x_626_, v___x_678_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_x_627_, v___x_680_);
v_newNode_682_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_623_, v_v_624_, v_node_674_, v___x_679_, v___x_681_, v_x_628_);
lean_inc_ref(v_newNode_682_);
v___x_683_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_685_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_newNode_682_);
v___x_685_ = v___x_676_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_newNode_682_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v___y_642_ = v___x_685_;
goto v___jp_641_;
}
}
else
{
lean_object* v_val_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_newNode_682_);
lean_del_object(v___x_676_);
v_val_687_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_683_, 1);
v_fst_688_ = lean_ctor_get(v_val_687_, 0);
v_snd_689_ = lean_ctor_get(v_val_687_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_val_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v_val_687_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_val_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_snd_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v___y_642_ = v___x_694_;
goto v___jp_641_;
}
}
}
}
}
default: 
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_623_, v_v_624_, v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_dec(v_x_628_);
v___y_642_ = v_v_638_;
goto v___jp_641_;
}
else
{
lean_object* v_val_700_; lean_object* v___x_701_; 
v_val_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_x_628_);
lean_ctor_set(v___x_701_, 1, v_val_700_);
v___y_642_ = v___x_701_;
goto v___jp_641_;
}
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_array_fset(v_xs_x27_640_, v_j_632_, v___y_642_);
lean_dec(v_j_632_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_643_);
v___x_645_ = v___x_636_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_object* v_ks_704_; lean_object* v_vs_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_738_; 
v_ks_704_ = lean_ctor_get(v_x_625_, 0);
v_vs_705_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_738_ == 0)
{
v___x_707_ = v_x_625_;
v_isShared_708_ = v_isSharedCheck_738_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_vs_705_);
lean_inc(v_ks_704_);
lean_dec(v_x_625_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_738_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; 
v___x_709_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(v_ks_704_, v_x_628_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_711_; 
if (v_isShared_708_ == 0)
{
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_ks_704_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_vs_705_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_box(0);
v___x_713_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_623_, v_v_624_, v___x_712_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec(v_x_628_);
return v___x_711_;
}
else
{
lean_object* v_val_714_; lean_object* v___x_715_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v___x_711_, v_x_626_, v_x_627_, v_x_628_, v_val_714_);
return v___x_715_;
}
}
}
else
{
lean_object* v_val_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_737_; 
v_val_717_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_737_ == 0)
{
v___x_719_ = v___x_709_;
v_isShared_720_ = v_isSharedCheck_737_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_val_717_);
lean_dec(v___x_709_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_737_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_v_x27_721_; lean_object* v_keys_722_; lean_object* v_vals_723_; lean_object* v___x_725_; 
v_v_x27_721_ = lean_array_fget(v_vs_705_, v_val_717_);
lean_inc(v_val_717_);
v_keys_722_ = l_Array_eraseIdx___redArg(v_ks_704_, v_val_717_);
v_vals_723_ = l_Array_eraseIdx___redArg(v_vs_705_, v_val_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_v_x27_721_);
v___x_725_ = v___x_719_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_v_x27_721_);
v___x_725_ = v_reuseFailAlloc_736_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_623_, v_v_624_, v___x_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_728_; 
lean_dec(v_x_628_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v_vals_723_);
lean_ctor_set(v___x_707_, 0, v_keys_722_);
v___x_728_ = v___x_707_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_keys_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_vals_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v_val_730_; lean_object* v_keys_731_; lean_object* v_vals_732_; lean_object* v___x_734_; 
v_val_730_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_726_, 1);
v_keys_731_ = lean_array_push(v_keys_722_, v_x_628_);
v_vals_732_ = lean_array_push(v_vals_723_, v_val_730_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v_vals_732_);
lean_ctor_set(v___x_707_, 0, v_keys_731_);
v___x_734_ = v___x_707_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_keys_731_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_vals_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___boxed(lean_object* v_keys_739_, lean_object* v_v_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
size_t v_x_2560__boxed_745_; size_t v_x_2561__boxed_746_; lean_object* v_res_747_; 
v_x_2560__boxed_745_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_x_2561__boxed_746_ = lean_unbox_usize(v_x_743_);
lean_dec(v_x_743_);
v_res_747_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_739_, v_v_740_, v_x_741_, v_x_2560__boxed_745_, v_x_2561__boxed_746_, v_x_744_);
lean_dec_ref(v_keys_739_);
return v_res_747_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object* v_msg_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0);
v___x_751_ = lean_panic_fn_borrowed(v___x_750_, v_msg_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_755_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2));
v___x_756_ = lean_unsigned_to_nat(23u);
v___x_757_ = lean_unsigned_to_nat(166u);
v___x_758_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1));
v___x_759_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0));
v___x_760_ = l_mkPanicMessageWithDecl(v___x_759_, v___x_758_, v___x_757_, v___x_756_, v___x_755_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object* v_d_761_, lean_object* v_keys_762_, lean_object* v_v_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_764_ = lean_array_get_size(v_keys_762_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_nat_dec_eq(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v_k_768_; uint64_t v___x_769_; size_t v_h_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_767_ = lean_box(0);
v_k_768_ = lean_array_get_borrowed(v___x_767_, v_keys_762_, v___x_765_);
v___x_769_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_768_);
v_h_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = ((size_t)1ULL);
lean_inc(v_k_768_);
v___x_772_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_762_, v_v_763_, v_d_761_, v_h_770_, v___x_771_, v_k_768_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v_v_763_);
lean_dec_ref(v_d_761_);
v___x_773_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
v___x_774_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object* v_d_775_, lean_object* v_keys_776_, lean_object* v_v_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_775_, v_keys_776_, v_v_777_);
lean_dec_ref(v_keys_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v_ks_783_; lean_object* v_vs_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_808_; 
v_ks_783_ = lean_ctor_get(v_x_779_, 0);
v_vs_784_ = lean_ctor_get(v_x_779_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_779_);
if (v_isSharedCheck_808_ == 0)
{
v___x_786_ = v_x_779_;
v_isShared_787_ = v_isSharedCheck_808_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_vs_784_);
lean_inc(v_ks_783_);
lean_dec(v_x_779_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_808_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_array_get_size(v_ks_783_);
v___x_789_ = lean_nat_dec_lt(v_x_780_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_dec(v_x_780_);
v___x_790_ = lean_array_push(v_ks_783_, v_x_781_);
v___x_791_ = lean_array_push(v_vs_784_, v_x_782_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_791_);
lean_ctor_set(v___x_786_, 0, v___x_790_);
v___x_793_ = v___x_786_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
lean_object* v_k_x27_795_; uint8_t v___x_796_; 
v_k_x27_795_ = lean_array_fget_borrowed(v_ks_783_, v_x_780_);
v___x_796_ = lean_name_eq(v_x_781_, v_k_x27_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_798_; 
if (v_isShared_787_ == 0)
{
v___x_798_ = v___x_786_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_ks_783_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_vs_784_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_x_780_, v___x_799_);
lean_dec(v_x_780_);
v_x_779_ = v___x_798_;
v_x_780_ = v___x_800_;
goto _start;
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_803_ = lean_array_fset(v_ks_783_, v_x_780_, v_x_781_);
v___x_804_ = lean_array_fset(v_vs_784_, v_x_780_, v_x_782_);
lean_dec(v_x_780_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_804_);
lean_ctor_set(v___x_786_, 0, v___x_803_);
v___x_806_ = v___x_786_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_809_, lean_object* v_k_810_, lean_object* v_v_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_809_, v___x_812_, v_k_810_, v_v_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_815_, size_t v_x_816_, size_t v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v_es_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v_j_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_es_820_ = lean_ctor_get(v_x_815_, 0);
v___x_821_ = ((size_t)31ULL);
v___x_822_ = lean_usize_land(v_x_816_, v___x_821_);
v_j_823_ = lean_usize_to_nat(v___x_822_);
v___x_824_ = lean_array_get_size(v_es_820_);
v___x_825_ = lean_nat_dec_lt(v_j_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v_j_823_);
lean_dec(v_x_819_);
lean_dec(v_x_818_);
return v_x_815_;
}
else
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_864_; 
lean_inc_ref(v_es_820_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v_x_815_, 0);
lean_dec(v_unused_865_);
v___x_827_ = v_x_815_;
v_isShared_828_ = v_isSharedCheck_864_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_x_815_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_864_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_v_829_; lean_object* v___x_830_; lean_object* v_xs_x27_831_; lean_object* v___y_833_; 
v_v_829_ = lean_array_fget(v_es_820_, v_j_823_);
v___x_830_ = lean_box(0);
v_xs_x27_831_ = lean_array_fset(v_es_820_, v_j_823_, v___x_830_);
switch(lean_obj_tag(v_v_829_))
{
case 0:
{
lean_object* v_key_838_; lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_849_; 
v_key_838_ = lean_ctor_get(v_v_829_, 0);
v_val_839_ = lean_ctor_get(v_v_829_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_v_829_);
if (v_isSharedCheck_849_ == 0)
{
v___x_841_ = v_v_829_;
v_isShared_842_ = v_isSharedCheck_849_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_inc(v_key_838_);
lean_dec(v_v_829_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_849_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v___x_843_; 
v___x_843_ = lean_name_eq(v_x_818_, v_key_838_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_841_);
v___x_844_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_838_, v_val_839_, v_x_818_, v_x_819_);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___y_833_ = v___x_845_;
goto v___jp_832_;
}
else
{
lean_object* v___x_847_; 
lean_dec(v_val_839_);
lean_dec(v_key_838_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_x_819_);
lean_ctor_set(v___x_841_, 0, v_x_818_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_x_818_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_x_819_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v___y_833_ = v___x_847_;
goto v___jp_832_;
}
}
}
}
case 1:
{
lean_object* v_node_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_862_; 
v_node_850_ = lean_ctor_get(v_v_829_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v_v_829_);
if (v_isSharedCheck_862_ == 0)
{
v___x_852_ = v_v_829_;
v_isShared_853_ = v_isSharedCheck_862_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_node_850_);
lean_dec(v_v_829_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_862_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_854_ = ((size_t)5ULL);
v___x_855_ = lean_usize_shift_right(v_x_816_, v___x_854_);
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_add(v_x_817_, v___x_856_);
v___x_858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_850_, v___x_855_, v___x_857_, v_x_818_, v_x_819_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_858_);
v___x_860_ = v___x_852_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
v___y_833_ = v___x_860_;
goto v___jp_832_;
}
}
}
default: 
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_x_818_);
lean_ctor_set(v___x_863_, 1, v_x_819_);
v___y_833_ = v___x_863_;
goto v___jp_832_;
}
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_array_fset(v_xs_x27_831_, v_j_823_, v___y_833_);
lean_dec(v_j_823_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_834_);
v___x_836_ = v___x_827_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
else
{
lean_object* v_ks_866_; lean_object* v_vs_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_887_; 
v_ks_866_ = lean_ctor_get(v_x_815_, 0);
v_vs_867_ = lean_ctor_get(v_x_815_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_887_ == 0)
{
v___x_869_ = v_x_815_;
v_isShared_870_ = v_isSharedCheck_887_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_vs_867_);
lean_inc(v_ks_866_);
lean_dec(v_x_815_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_887_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_ks_866_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_vs_867_);
v___x_872_ = v_reuseFailAlloc_886_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v_newNode_873_; uint8_t v___y_875_; size_t v___x_881_; uint8_t v___x_882_; 
v_newNode_873_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_872_, v_x_818_, v_x_819_);
v___x_881_ = ((size_t)7ULL);
v___x_882_ = lean_usize_dec_le(v___x_881_, v_x_817_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_873_);
v___x_884_ = lean_unsigned_to_nat(4u);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
lean_dec(v___x_883_);
v___y_875_ = v___x_885_;
goto v___jp_874_;
}
else
{
v___y_875_ = v___x_882_;
goto v___jp_874_;
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
lean_object* v_ks_876_; lean_object* v_vs_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_ks_876_ = lean_ctor_get(v_newNode_873_, 0);
lean_inc_ref(v_ks_876_);
v_vs_877_ = lean_ctor_get(v_newNode_873_, 1);
lean_inc_ref(v_vs_877_);
lean_dec_ref(v_newNode_873_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0);
v___x_880_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_817_, v_ks_876_, v_vs_877_, v___x_878_, v___x_879_);
lean_dec_ref(v_vs_877_);
lean_dec_ref(v_ks_876_);
return v___x_880_;
}
else
{
return v_newNode_873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_888_, lean_object* v_keys_889_, lean_object* v_vals_890_, lean_object* v_i_891_, lean_object* v_entries_892_){
_start:
{
lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = lean_array_get_size(v_keys_889_);
v___x_894_ = lean_nat_dec_lt(v_i_891_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec(v_i_891_);
return v_entries_892_;
}
else
{
lean_object* v_k_895_; lean_object* v_v_896_; uint64_t v___y_898_; 
v_k_895_ = lean_array_fget_borrowed(v_keys_889_, v_i_891_);
v_v_896_ = lean_array_fget_borrowed(v_vals_890_, v_i_891_);
if (lean_obj_tag(v_k_895_) == 0)
{
uint64_t v___x_909_; 
v___x_909_ = 1723ULL;
v___y_898_ = v___x_909_;
goto v___jp_897_;
}
else
{
uint64_t v_hash_910_; 
v_hash_910_ = lean_ctor_get_uint64(v_k_895_, sizeof(void*)*2);
v___y_898_ = v_hash_910_;
goto v___jp_897_;
}
v___jp_897_:
{
size_t v_h_899_; size_t v___x_900_; lean_object* v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; size_t v_h_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_h_899_ = lean_uint64_to_usize(v___y_898_);
v___x_900_ = ((size_t)5ULL);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_sub(v_depth_888_, v___x_902_);
v___x_904_ = lean_usize_mul(v___x_900_, v___x_903_);
v_h_905_ = lean_usize_shift_right(v_h_899_, v___x_904_);
v___x_906_ = lean_nat_add(v_i_891_, v___x_901_);
lean_dec(v_i_891_);
lean_inc(v_v_896_);
lean_inc(v_k_895_);
v___x_907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_892_, v_h_905_, v_depth_888_, v_k_895_, v_v_896_);
v_i_891_ = v___x_906_;
v_entries_892_ = v___x_907_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_911_, lean_object* v_keys_912_, lean_object* v_vals_913_, lean_object* v_i_914_, lean_object* v_entries_915_){
_start:
{
size_t v_depth_boxed_916_; lean_object* v_res_917_; 
v_depth_boxed_916_ = lean_unbox_usize(v_depth_911_);
lean_dec(v_depth_911_);
v_res_917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_916_, v_keys_912_, v_vals_913_, v_i_914_, v_entries_915_);
lean_dec_ref(v_vals_913_);
lean_dec_ref(v_keys_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
size_t v_x_2904__boxed_923_; size_t v_x_2905__boxed_924_; lean_object* v_res_925_; 
v_x_2904__boxed_923_ = lean_unbox_usize(v_x_919_);
lean_dec(v_x_919_);
v_x_2905__boxed_924_ = lean_unbox_usize(v_x_920_);
lean_dec(v_x_920_);
v_res_925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_918_, v_x_2904__boxed_923_, v_x_2905__boxed_924_, v_x_921_, v_x_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
uint64_t v___y_930_; 
if (lean_obj_tag(v_x_927_) == 0)
{
uint64_t v___x_934_; 
v___x_934_ = 1723ULL;
v___y_930_ = v___x_934_;
goto v___jp_929_;
}
else
{
uint64_t v_hash_935_; 
v_hash_935_ = lean_ctor_get_uint64(v_x_927_, sizeof(void*)*2);
v___y_930_ = v_hash_935_;
goto v___jp_929_;
}
v___jp_929_:
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_uint64_to_usize(v___y_930_);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_926_, v___x_931_, v___x_932_, v_x_927_, v_x_928_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object* v_xs_936_, lean_object* v_v_937_, lean_object* v_i_938_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = lean_array_get_size(v_xs_936_);
v___x_940_ = lean_nat_dec_lt(v_i_938_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec(v_i_938_);
v___x_941_ = lean_box(0);
return v___x_941_;
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_array_fget_borrowed(v_xs_936_, v_i_938_);
v___x_943_ = lean_name_eq(v___x_942_, v_v_937_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_i_938_, v___x_944_);
lean_dec(v_i_938_);
v_i_938_ = v___x_945_;
goto _start;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v_i_938_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_xs_948_, lean_object* v_v_949_, lean_object* v_i_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_948_, v_v_949_, v_i_950_);
lean_dec(v_v_949_);
lean_dec_ref(v_xs_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object* v_xs_952_, lean_object* v_v_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_952_, v_v_953_, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object* v_xs_956_, lean_object* v_v_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_956_, v_v_957_);
lean_dec(v_v_957_);
lean_dec_ref(v_xs_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object* v_x_959_, size_t v_x_960_, lean_object* v_x_961_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
lean_object* v_es_962_; lean_object* v___x_963_; size_t v___x_964_; size_t v___x_965_; lean_object* v_j_966_; lean_object* v_entry_967_; 
v_es_962_ = lean_ctor_get(v_x_959_, 0);
v___x_963_ = lean_box(2);
v___x_964_ = ((size_t)31ULL);
v___x_965_ = lean_usize_land(v_x_960_, v___x_964_);
v_j_966_ = lean_usize_to_nat(v___x_965_);
v_entry_967_ = lean_array_get(v___x_963_, v_es_962_, v_j_966_);
switch(lean_obj_tag(v_entry_967_))
{
case 0:
{
lean_object* v_key_968_; uint8_t v___x_969_; 
v_key_968_ = lean_ctor_get(v_entry_967_, 0);
lean_inc(v_key_968_);
lean_dec_ref_known(v_entry_967_, 2);
v___x_969_ = lean_name_eq(v_x_961_, v_key_968_);
lean_dec(v_key_968_);
if (v___x_969_ == 0)
{
lean_dec(v_j_966_);
return v_x_959_;
}
else
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
lean_inc_ref(v_es_962_);
v_isSharedCheck_977_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v_x_959_, 0);
lean_dec(v_unused_978_);
v___x_971_ = v_x_959_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_dec(v_x_959_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_array_set(v_es_962_, v_j_966_, v___x_963_);
lean_dec(v_j_966_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
case 1:
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1013_; 
lean_inc_ref(v_es_962_);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v_x_959_, 0);
lean_dec(v_unused_1014_);
v___x_980_ = v_x_959_;
v_isShared_981_ = v_isSharedCheck_1013_;
goto v_resetjp_979_;
}
else
{
lean_dec(v_x_959_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1013_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_node_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1012_; 
v_node_982_ = lean_ctor_get(v_entry_967_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_entry_967_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_984_ = v_entry_967_;
v_isShared_985_ = v_isSharedCheck_1012_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_node_982_);
lean_dec(v_entry_967_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1012_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
size_t v___x_986_; lean_object* v_entries_987_; size_t v___x_988_; lean_object* v_newNode_989_; lean_object* v___x_990_; 
v___x_986_ = ((size_t)5ULL);
v_entries_987_ = lean_array_set(v_es_962_, v_j_966_, v___x_963_);
v___x_988_ = lean_usize_shift_right(v_x_960_, v___x_986_);
v_newNode_989_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_982_, v___x_988_, v_x_961_);
lean_inc_ref(v_newNode_989_);
v___x_990_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_992_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_newNode_989_);
v___x_992_ = v___x_984_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_newNode_989_);
v___x_992_ = v_reuseFailAlloc_997_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_array_set(v_entries_987_, v_j_966_, v___x_992_);
lean_dec(v_j_966_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_993_);
v___x_995_ = v___x_980_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_val_998_; lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_newNode_989_);
lean_del_object(v___x_984_);
v_val_998_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v___x_990_, 1);
v_fst_999_ = lean_ctor_get(v_val_998_, 0);
v_snd_1000_ = lean_ctor_get(v_val_998_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_val_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1002_ = v_val_998_;
v_isShared_1003_ = v_isSharedCheck_1011_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_snd_1000_);
lean_inc(v_fst_999_);
lean_dec(v_val_998_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1011_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_fst_999_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_snd_1000_);
v___x_1005_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = lean_array_set(v_entries_987_, v_j_966_, v___x_1005_);
lean_dec(v_j_966_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_1006_);
v___x_1008_ = v___x_980_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_966_);
return v_x_959_;
}
}
}
else
{
lean_object* v_ks_1015_; lean_object* v_vs_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1030_; 
v_ks_1015_ = lean_ctor_get(v_x_959_, 0);
v_vs_1016_ = lean_ctor_get(v_x_959_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1018_ = v_x_959_;
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_vs_1016_);
lean_inc(v_ks_1015_);
lean_dec(v_x_959_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1030_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_1015_, v_x_961_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1022_; 
if (v_isShared_1019_ == 0)
{
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_ks_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_vs_1016_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
lean_object* v_val_1024_; lean_object* v_keys_x27_1025_; lean_object* v_vals_x27_1026_; lean_object* v___x_1028_; 
v_val_1024_ = lean_ctor_get(v___x_1020_, 0);
lean_inc_n(v_val_1024_, 2);
lean_dec_ref_known(v___x_1020_, 1);
v_keys_x27_1025_ = l_Array_eraseIdx___redArg(v_ks_1015_, v_val_1024_);
v_vals_x27_1026_ = l_Array_eraseIdx___redArg(v_vs_1016_, v_val_1024_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_vals_x27_1026_);
lean_ctor_set(v___x_1018_, 0, v_keys_x27_1025_);
v___x_1028_ = v___x_1018_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_keys_x27_1025_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_vals_x27_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
size_t v_x_3102__boxed_1034_; lean_object* v_res_1035_; 
v_x_3102__boxed_1034_ = lean_unbox_usize(v_x_1032_);
lean_dec(v_x_1032_);
v_res_1035_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1031_, v_x_3102__boxed_1034_, v_x_1033_);
lean_dec(v_x_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
uint64_t v___y_1039_; 
if (lean_obj_tag(v_x_1037_) == 0)
{
uint64_t v___x_1042_; 
v___x_1042_ = 1723ULL;
v___y_1039_ = v___x_1042_;
goto v___jp_1038_;
}
else
{
uint64_t v_hash_1043_; 
v_hash_1043_ = lean_ctor_get_uint64(v_x_1037_, sizeof(void*)*2);
v___y_1039_ = v_hash_1043_;
goto v___jp_1038_;
}
v___jp_1038_:
{
size_t v_h_1040_; lean_object* v___x_1041_; 
v_h_1040_ = lean_uint64_to_usize(v___y_1039_);
v___x_1041_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1036_, v_h_1040_, v_x_1037_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1044_, v_x_1045_);
lean_dec(v_x_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object* v_s_1047_, lean_object* v_keys_1048_, lean_object* v_declName_1049_, uint8_t v_phase_1050_, lean_object* v_proc_1051_){
_start:
{
lean_object* v_pre_1052_; lean_object* v_eval_1053_; lean_object* v_post_1054_; lean_object* v_simprocNames_1055_; lean_object* v_erased_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1077_; 
v_pre_1052_ = lean_ctor_get(v_s_1047_, 0);
v_eval_1053_ = lean_ctor_get(v_s_1047_, 1);
v_post_1054_ = lean_ctor_get(v_s_1047_, 2);
v_simprocNames_1055_ = lean_ctor_get(v_s_1047_, 3);
v_erased_1056_ = lean_ctor_get(v_s_1047_, 4);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_s_1047_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1058_ = v_s_1047_;
v_isShared_1059_ = v_isSharedCheck_1077_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_erased_1056_);
lean_inc(v_simprocNames_1055_);
lean_inc(v_post_1054_);
lean_inc(v_eval_1053_);
lean_inc(v_pre_1052_);
lean_dec(v_s_1047_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1077_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v_entry_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_inc_ref(v_keys_1048_);
lean_inc_n(v_declName_1049_, 2);
v___x_1060_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1060_, 0, v_declName_1049_);
lean_ctor_set(v___x_1060_, 1, v_keys_1048_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*2, v_phase_1050_);
v_entry_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_entry_1061_, 0, v___x_1060_);
lean_ctor_set(v_entry_1061_, 1, v_proc_1051_);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_1055_, v_declName_1049_, v___x_1062_);
v___x_1064_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_1056_, v_declName_1049_);
lean_dec(v_declName_1049_);
switch(v_phase_1050_)
{
case 0:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_1052_, v_keys_1048_, v_entry_1061_);
lean_dec_ref(v_keys_1048_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___x_1064_);
lean_ctor_set(v___x_1058_, 3, v___x_1063_);
lean_ctor_set(v___x_1058_, 0, v___x_1065_);
v___x_1067_ = v___x_1058_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_eval_1053_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_post_1054_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v___x_1064_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
case 1:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_1053_, v_keys_1048_, v_entry_1061_);
lean_dec_ref(v_keys_1048_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___x_1064_);
lean_ctor_set(v___x_1058_, 3, v___x_1063_);
lean_ctor_set(v___x_1058_, 1, v___x_1069_);
v___x_1071_ = v___x_1058_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_pre_1052_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_post_1054_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v___x_1064_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
default: 
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_1054_, v_keys_1048_, v_entry_1061_);
lean_dec_ref(v_keys_1048_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___x_1064_);
lean_ctor_set(v___x_1058_, 3, v___x_1063_);
lean_ctor_set(v___x_1058_, 2, v___x_1073_);
v___x_1075_ = v___x_1058_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_pre_1052_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_eval_1053_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___x_1064_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object* v_s_1078_, lean_object* v_keys_1079_, lean_object* v_declName_1080_, lean_object* v_phase_1081_, lean_object* v_proc_1082_){
_start:
{
uint8_t v_phase_boxed_1083_; lean_object* v_res_1084_; 
v_phase_boxed_1083_ = lean_unbox(v_phase_1081_);
v_res_1084_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_1078_, v_keys_1079_, v_declName_1080_, v_phase_boxed_1083_, v_proc_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_1086_, v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(v_00_u03b2_1094_, v_x_1095_, v_x_1096_);
lean_dec(v_x_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, size_t v_x_1100_, size_t v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1099_, v_x_1100_, v_x_1101_, v_x_1102_, v_x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
size_t v_x_3308__boxed_1111_; size_t v_x_3309__boxed_1112_; lean_object* v_res_1113_; 
v_x_3308__boxed_1111_ = lean_unbox_usize(v_x_1107_);
lean_dec(v_x_1107_);
v_x_3309__boxed_1112_ = lean_unbox_usize(v_x_1108_);
lean_dec(v_x_1108_);
v_res_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_1105_, v_x_1106_, v_x_3308__boxed_1111_, v_x_3309__boxed_1112_, v_x_1109_, v_x_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, size_t v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1115_, v_x_1116_, v_x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
size_t v_x_3325__boxed_1123_; lean_object* v_res_1124_; 
v_x_3325__boxed_1123_ = lean_unbox_usize(v_x_1121_);
lean_dec(v_x_1121_);
v_res_1124_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_1119_, v_x_1120_, v_x_3325__boxed_1123_, v_x_1122_);
lean_dec(v_x_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1125_, lean_object* v_n_1126_, lean_object* v_k_1127_, lean_object* v_v_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_1126_, v_k_1127_, v_v_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1130_, size_t v_depth_1131_, lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_heq_1134_, lean_object* v_i_1135_, lean_object* v_entries_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_1131_, v_keys_1132_, v_vals_1133_, v_i_1135_, v_entries_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1138_, lean_object* v_depth_1139_, lean_object* v_keys_1140_, lean_object* v_vals_1141_, lean_object* v_heq_1142_, lean_object* v_i_1143_, lean_object* v_entries_1144_){
_start:
{
size_t v_depth_boxed_1145_; lean_object* v_res_1146_; 
v_depth_boxed_1145_ = lean_unbox_usize(v_depth_1139_);
lean_dec(v_depth_1139_);
v_res_1146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_1138_, v_depth_boxed_1145_, v_keys_1140_, v_vals_1141_, v_heq_1142_, v_i_1143_, v_entries_1144_);
lean_dec_ref(v_vals_1141_);
lean_dec_ref(v_keys_1140_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(lean_object* v_00_u03b2_1147_, lean_object* v_x_1148_, size_t v_x_1149_, size_t v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_x_1148_, v_x_1149_, v_x_1150_, v_x_1151_, v_x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
size_t v_x_3340__boxed_1160_; size_t v_x_3341__boxed_1161_; lean_object* v_res_1162_; 
v_x_3340__boxed_1160_ = lean_unbox_usize(v_x_1156_);
lean_dec(v_x_1156_);
v_x_3341__boxed_1161_ = lean_unbox_usize(v_x_1157_);
lean_dec(v_x_1157_);
v_res_1162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(v_00_u03b2_1154_, v_x_1155_, v_x_3340__boxed_1160_, v_x_3341__boxed_1161_, v_x_1158_, v_x_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1164_, v_x_1165_, v_x_1166_, v_x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(lean_object* v_x_1169_, lean_object* v_keys_1170_, lean_object* v_v_1171_, lean_object* v_k_1172_, lean_object* v_as_1173_, lean_object* v_k_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_1169_, v_keys_1170_, v_v_1171_, v_k_1172_, v_as_1173_, v_k_1174_, v_x_1175_, v_x_1176_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___boxed(lean_object* v_x_1180_, lean_object* v_keys_1181_, lean_object* v_v_1182_, lean_object* v_k_1183_, lean_object* v_as_1184_, lean_object* v_k_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(v_x_1180_, v_keys_1181_, v_v_1182_, v_k_1183_, v_as_1184_, v_k_1185_, v_x_1186_, v_x_1187_, v_x_1188_, v_x_1189_);
lean_dec_ref(v_k_1185_);
lean_dec_ref(v_keys_1181_);
lean_dec(v_x_1180_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(lean_object* v_00_u03b2_1191_, lean_object* v_n_1192_, lean_object* v_k_1193_, lean_object* v_v_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(v_n_1192_, v_k_1193_, v_v_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(lean_object* v_00_u03b2_1196_, size_t v_depth_1197_, lean_object* v_keys_1198_, lean_object* v_vals_1199_, lean_object* v_heq_1200_, lean_object* v_i_1201_, lean_object* v_entries_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_depth_1197_, v_keys_1198_, v_vals_1199_, v_i_1201_, v_entries_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___boxed(lean_object* v_00_u03b2_1204_, lean_object* v_depth_1205_, lean_object* v_keys_1206_, lean_object* v_vals_1207_, lean_object* v_heq_1208_, lean_object* v_i_1209_, lean_object* v_entries_1210_){
_start:
{
size_t v_depth_boxed_1211_; lean_object* v_res_1212_; 
v_depth_boxed_1211_ = lean_unbox_usize(v_depth_1205_);
lean_dec(v_depth_1205_);
v_res_1212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(v_00_u03b2_1204_, v_depth_boxed_1211_, v_keys_1206_, v_vals_1207_, v_heq_1208_, v_i_1209_, v_entries_1210_);
lean_dec_ref(v_vals_1207_);
lean_dec_ref(v_keys_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20(lean_object* v_00_u03b2_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(v_x_1214_, v_x_1215_, v_x_1216_, v_x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object* v_s_1219_, lean_object* v_declName_1220_){
_start:
{
lean_object* v_pre_1221_; lean_object* v_eval_1222_; lean_object* v_post_1223_; lean_object* v_simprocNames_1224_; lean_object* v_erased_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1235_; 
v_pre_1221_ = lean_ctor_get(v_s_1219_, 0);
v_eval_1222_ = lean_ctor_get(v_s_1219_, 1);
v_post_1223_ = lean_ctor_get(v_s_1219_, 2);
v_simprocNames_1224_ = lean_ctor_get(v_s_1219_, 3);
v_erased_1225_ = lean_ctor_get(v_s_1219_, 4);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_s_1219_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1227_ = v_s_1219_;
v_isShared_1228_ = v_isSharedCheck_1235_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_erased_1225_);
lean_inc(v_simprocNames_1224_);
lean_inc(v_post_1223_);
lean_inc(v_eval_1222_);
lean_inc(v_pre_1221_);
lean_dec(v_s_1219_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1235_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1229_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_1224_, v_declName_1220_);
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_1225_, v_declName_1220_, v___x_1230_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 4, v___x_1231_);
lean_ctor_set(v___x_1227_, 3, v___x_1229_);
v___x_1233_ = v___x_1227_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_pre_1221_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_eval_1222_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_post_1223_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v_cellCount_1236_; lean_object* v___x_1237_; 
v_cellCount_1236_ = lean_unsigned_to_nat(16u);
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v_cellCount_1238_; lean_object* v___x_1239_; 
v_cellCount_1238_ = lean_unsigned_to_nat(16u);
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1240_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___x_1241_);
lean_ctor_set(v___x_1243_, 2, v___x_1240_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default(void){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3);
return v___x_1246_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs(void){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__3);
v___x_1250_ = lean_st_mk_ref(v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object* v_m_1254_, lean_object* v_query_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_zero_1259_; uint8_t v_isZero_1260_; 
v_zero_1259_ = lean_unsigned_to_nat(0u);
v_isZero_1260_ = lean_nat_dec_eq(v_x_1257_, v_zero_1259_);
if (v_isZero_1260_ == 1)
{
lean_dec(v_x_1258_);
lean_dec(v_x_1257_);
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_box(2);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_val_1262_ = lean_ctor_get(v_x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v_x_1256_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_val_1262_);
lean_dec(v_x_1256_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_val_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_keyArray_1270_; lean_object* v_valueArray_1271_; lean_object* v___x_1272_; uint8_t v_isSome_1273_; 
v_keyArray_1270_ = lean_ctor_get(v_m_1254_, 1);
v_valueArray_1271_ = lean_ctor_get(v_m_1254_, 2);
v___x_1272_ = lean_array_fget_borrowed(v_keyArray_1270_, v_x_1258_);
v_isSome_1273_ = lean_noption_is_some(v___x_1272_);
if (v_isSome_1273_ == 0)
{
lean_dec(v_x_1257_);
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_x_1258_);
return v___x_1274_;
}
else
{
lean_object* v_val_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_x_1258_);
v_val_1275_ = lean_ctor_get(v_x_1256_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_x_1256_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v_x_1256_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_val_1275_);
lean_dec(v_x_1256_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_val_1275_);
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
else
{
lean_object* v_one_1283_; lean_object* v_n_1284_; lean_object* v___y_1286_; 
v_one_1283_ = lean_unsigned_to_nat(1u);
v_n_1284_ = lean_nat_sub(v_x_1257_, v_one_1283_);
lean_dec(v_x_1257_);
if (v_isSome_1273_ == 0)
{
goto v___jp_1292_;
}
else
{
lean_object* v___x_1294_; uint8_t v_isSome_1295_; 
v___x_1294_ = lean_array_fget_borrowed(v_valueArray_1271_, v_x_1258_);
v_isSome_1295_ = lean_noption_is_some(v___x_1294_);
if (v_isSome_1295_ == 0)
{
goto v___jp_1292_;
}
else
{
lean_object* v_val_1296_; uint8_t v___x_1297_; 
lean_inc(v___x_1272_);
v_val_1296_ = lean_noption_get(v___x_1272_);
v___x_1297_ = lean_name_eq(v_val_1296_, v_query_1255_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
lean_dec(v_val_1296_);
v___x_1298_ = lean_array_get_size(v_keyArray_1270_);
v___x_1299_ = lean_nat_add(v_x_1258_, v_one_1283_);
lean_dec(v_x_1258_);
v___x_1300_ = lean_nat_dec_lt(v___x_1299_, v___x_1298_);
if (v___x_1300_ == 0)
{
lean_dec(v___x_1299_);
v_x_1257_ = v_n_1284_;
v_x_1258_ = v_zero_1259_;
goto _start;
}
else
{
v_x_1257_ = v_n_1284_;
v_x_1258_ = v___x_1299_;
goto _start;
}
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1304_; 
lean_dec(v_n_1284_);
lean_dec(v_x_1256_);
lean_inc(v___x_1294_);
v_val_1303_ = lean_noption_get(v___x_1294_);
v___x_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1304_, 0, v_x_1258_);
lean_ctor_set(v___x_1304_, 1, v_val_1296_);
lean_ctor_set(v___x_1304_, 2, v_val_1303_);
return v___x_1304_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1287_ = lean_array_get_size(v_keyArray_1270_);
v___x_1288_ = lean_nat_add(v_x_1258_, v_one_1283_);
lean_dec(v_x_1258_);
v___x_1289_ = lean_nat_dec_lt(v___x_1288_, v___x_1287_);
if (v___x_1289_ == 0)
{
lean_dec(v___x_1288_);
v_x_1256_ = v___y_1286_;
v_x_1257_ = v_n_1284_;
v_x_1258_ = v_zero_1259_;
goto _start;
}
else
{
v_x_1256_ = v___y_1286_;
v_x_1257_ = v_n_1284_;
v_x_1258_ = v___x_1288_;
goto _start;
}
}
v___jp_1292_:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v___x_1293_; 
lean_inc(v_x_1258_);
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_x_1258_);
v___y_1286_ = v___x_1293_;
goto v___jp_1285_;
}
else
{
v___y_1286_ = v_x_1256_;
goto v___jp_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg___boxed(lean_object* v_m_1305_, lean_object* v_query_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_m_1305_, v_query_1306_, v_x_1307_, v_x_1308_, v_x_1309_);
lean_dec(v_query_1306_);
lean_dec_ref(v_m_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object* v_m_1311_, lean_object* v_query_1312_){
_start:
{
lean_object* v_keyArray_1313_; lean_object* v___x_1314_; uint64_t v___y_1316_; 
v_keyArray_1313_ = lean_ctor_get(v_m_1311_, 1);
v___x_1314_ = lean_array_get_size(v_keyArray_1313_);
if (lean_obj_tag(v_query_1312_) == 0)
{
uint64_t v___x_1331_; 
v___x_1331_ = 1723ULL;
v___y_1316_ = v___x_1331_;
goto v___jp_1315_;
}
else
{
uint64_t v_hash_1332_; 
v_hash_1332_ = lean_ctor_get_uint64(v_query_1312_, sizeof(void*)*2);
v___y_1316_ = v_hash_1332_;
goto v___jp_1315_;
}
v___jp_1315_:
{
uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v_fold_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1317_ = 32ULL;
v___x_1318_ = lean_uint64_shift_right(v___y_1316_, v___x_1317_);
v_fold_1319_ = lean_uint64_xor(v___y_1316_, v___x_1318_);
v___x_1320_ = 16ULL;
v___x_1321_ = lean_uint64_shift_right(v_fold_1319_, v___x_1320_);
v___x_1322_ = lean_uint64_xor(v_fold_1319_, v___x_1321_);
v___x_1323_ = lean_uint64_to_usize(v___x_1322_);
v___x_1324_ = lean_usize_of_nat(v___x_1314_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_sub(v___x_1324_, v___x_1325_);
v___x_1327_ = lean_usize_land(v___x_1323_, v___x_1326_);
v___x_1328_ = lean_usize_to_nat(v___x_1327_);
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_m_1311_, v_query_1312_, v___x_1329_, v___x_1314_, v___x_1328_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg___boxed(lean_object* v_m_1333_, lean_object* v_query_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1333_, v_query_1334_);
lean_dec(v_query_1334_);
lean_dec_ref(v_m_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object* v_m_1336_, lean_object* v_query_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1336_, v_query_1337_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_index_1339_; lean_object* v_key_1340_; lean_object* v_value_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_index_1339_ = lean_ctor_get(v___x_1338_, 0);
v_key_1340_ = lean_ctor_get(v___x_1338_, 1);
v_value_1341_ = lean_ctor_get(v___x_1338_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1338_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_value_1341_);
lean_inc(v_key_1340_);
lean_inc(v_index_1339_);
lean_dec(v___x_1338_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
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
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_index_1339_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_key_1340_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_value_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v___x_1349_; 
lean_dec(v___x_1338_);
v___x_1349_ = lean_box(1);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_m_1350_, lean_object* v_query_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_m_1350_, v_query_1351_);
lean_dec(v_query_1351_);
lean_dec_ref(v_m_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object* v_m_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_m_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
uint8_t v___x_1356_; 
lean_dec_ref_known(v___x_1355_, 3);
v___x_1356_ = 1;
return v___x_1356_;
}
else
{
uint8_t v___x_1357_; 
v___x_1357_ = 0;
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object* v_m_1358_, lean_object* v_a_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_m_1358_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg(lean_object* v_b_1362_, lean_object* v_acc_1363_, lean_object* v_i_1364_){
_start:
{
lean_object* v___y_1366_; lean_object* v_keyArray_1374_; lean_object* v_valueArray_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_keyArray_1374_ = lean_ctor_get(v_b_1362_, 1);
v_valueArray_1375_ = lean_ctor_get(v_b_1362_, 2);
v___x_1376_ = lean_array_get_size(v_keyArray_1374_);
v___x_1377_ = lean_nat_dec_lt(v_i_1364_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec(v_i_1364_);
return v_acc_1363_;
}
else
{
lean_object* v___x_1378_; uint8_t v_isSome_1379_; 
v___x_1378_ = lean_array_fget_borrowed(v_keyArray_1374_, v_i_1364_);
v_isSome_1379_ = lean_noption_is_some(v___x_1378_);
if (v_isSome_1379_ == 0)
{
goto v___jp_1370_;
}
else
{
lean_object* v___x_1380_; uint8_t v_isSome_1381_; 
v___x_1380_ = lean_array_fget_borrowed(v_valueArray_1375_, v_i_1364_);
v_isSome_1381_ = lean_noption_is_some(v___x_1380_);
if (v_isSome_1381_ == 0)
{
goto v___jp_1370_;
}
else
{
lean_object* v_val_1382_; lean_object* v_val_1383_; lean_object* v_i_1385_; lean_object* v___x_1390_; 
lean_inc(v___x_1378_);
v_val_1382_ = lean_noption_get(v___x_1378_);
lean_inc(v___x_1380_);
v_val_1383_ = lean_noption_get(v___x_1380_);
v___x_1390_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_acc_1363_, v_val_1382_);
switch(lean_obj_tag(v___x_1390_))
{
case 0:
{
lean_object* v_index_1391_; lean_object* v_size_1392_; lean_object* v___x_1393_; 
v_index_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_index_1391_);
lean_dec_ref_known(v___x_1390_, 3);
v_size_1392_ = lean_ctor_get(v_acc_1363_, 0);
lean_inc(v_size_1392_);
v___x_1393_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1363_, v_size_1392_, v_index_1391_, v_val_1382_, v_val_1383_);
lean_dec(v_index_1391_);
v___y_1366_ = v___x_1393_;
goto v___jp_1365_;
}
case 1:
{
lean_object* v_index_1394_; 
v_index_1394_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_index_1394_);
lean_dec_ref_known(v___x_1390_, 1);
v_i_1385_ = v_index_1394_;
goto v___jp_1384_;
}
default: 
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1363_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_index_1397_; 
v_index_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_index_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v_i_1385_ = v_index_1397_;
goto v___jp_1384_;
}
else
{
lean_dec(v_val_1383_);
lean_dec(v_val_1382_);
v___y_1366_ = v_acc_1363_;
goto v___jp_1365_;
}
}
}
v___jp_1384_:
{
lean_object* v_size_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_size_1386_ = lean_ctor_get(v_acc_1363_, 0);
v___x_1387_ = lean_unsigned_to_nat(1u);
v___x_1388_ = lean_nat_add(v_size_1386_, v___x_1387_);
v___x_1389_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1363_, v___x_1388_, v_i_1385_, v_val_1382_, v_val_1383_);
lean_dec(v_i_1385_);
v___y_1366_ = v___x_1389_;
goto v___jp_1365_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_i_1364_, v___x_1367_);
lean_dec(v_i_1364_);
v_acc_1363_ = v___y_1366_;
v_i_1364_ = v___x_1368_;
goto _start;
}
v___jp_1370_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_i_1364_, v___x_1371_);
lean_dec(v_i_1364_);
v_i_1364_ = v___x_1372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_1398_, lean_object* v_acc_1399_, lean_object* v_i_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg(v_b_1398_, v_acc_1399_, v_i_1400_);
lean_dec_ref(v_b_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg(lean_object* v_init_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg(v_b_1403_, v_init_1402_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg___boxed(lean_object* v_init_1406_, lean_object* v_b_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg(v_init_1406_, v_b_1407_);
lean_dec_ref(v_b_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(lean_object* v_m_1409_){
_start:
{
lean_object* v_keyArray_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_cellCount_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_target_1417_; lean_object* v___x_1418_; 
v_keyArray_1410_ = lean_ctor_get(v_m_1409_, 1);
v___x_1411_ = lean_array_get_size(v_keyArray_1410_);
v___x_1412_ = lean_unsigned_to_nat(2u);
v_cellCount_1413_ = lean_nat_mul(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1413_);
v___x_1415_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1413_);
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1413_);
v_target_1417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1417_, 0, v___x_1414_);
lean_ctor_set(v_target_1417_, 1, v___x_1415_);
lean_ctor_set(v_target_1417_, 2, v___x_1416_);
v___x_1418_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg(v_target_1417_, v_m_1409_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg___boxed(lean_object* v_m_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_m_1419_);
lean_dec_ref(v_m_1419_);
return v_res_1420_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0));
v___x_1423_ = lean_mk_io_user_error(v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object* v_declName_1426_, lean_object* v_keys_1427_, lean_object* v_proc_1428_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = l_Lean_initializing();
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_proc_1428_);
lean_dec_ref(v_keys_1427_);
lean_dec(v_declName_1426_);
v___x_1431_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_keys_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1593_; 
v___x_1433_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_1434_ = lean_st_ref_get(v___x_1433_);
v_keys_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v___x_1434_, 1);
lean_dec(v_unused_1594_);
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1593_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_keys_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1593_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_1435_, v_declName_1426_);
lean_dec_ref(v_keys_1435_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v_i_1452_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v_i_1471_; lean_object* v_keys_1476_; lean_object* v_procs_1477_; lean_object* v___y_1479_; lean_object* v___y_1490_; lean_object* v___y_1522_; lean_object* v_i_1523_; lean_object* v___y_1529_; lean_object* v___y_1539_; lean_object* v_i_1540_; lean_object* v___x_1555_; 
v___x_1440_ = lean_st_ref_take(v___x_1433_);
v_keys_1476_ = lean_ctor_get(v___x_1440_, 0);
lean_inc_ref(v_keys_1476_);
v_procs_1477_ = lean_ctor_get(v___x_1440_, 1);
lean_inc_ref(v_procs_1477_);
lean_dec(v___x_1440_);
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_1476_, v_declName_1426_);
switch(lean_obj_tag(v___x_1555_))
{
case 0:
{
lean_object* v_index_1556_; lean_object* v_size_1557_; lean_object* v___x_1558_; 
v_index_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_index_1556_);
lean_dec_ref_known(v___x_1555_, 3);
v_size_1557_ = lean_ctor_get(v_keys_1476_, 0);
lean_inc(v_size_1557_);
lean_inc(v_declName_1426_);
v___x_1558_ = l_Std_DHashMap_Raw_setEntry___redArg(v_keys_1476_, v_size_1557_, v_index_1556_, v_declName_1426_, v_keys_1427_);
lean_dec(v_index_1556_);
v___y_1490_ = v___x_1558_;
goto v___jp_1489_;
}
case 1:
{
lean_object* v_index_1559_; lean_object* v_size_1560_; lean_object* v_keyArray_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_index_1559_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_index_1559_);
lean_dec_ref_known(v___x_1555_, 1);
v_size_1560_ = lean_ctor_get(v_keys_1476_, 0);
v_keyArray_1561_ = lean_ctor_get(v_keys_1476_, 1);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_add(v_size_1560_, v___x_1562_);
v___x_1564_ = lean_array_get_size(v_keyArray_1561_);
v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_dec(v___x_1563_);
lean_dec(v_index_1559_);
goto v___jp_1545_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1566_ = lean_unsigned_to_nat(4u);
v___x_1567_ = lean_nat_mul(v___x_1563_, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(3u);
v___x_1569_ = lean_nat_mul(v___x_1564_, v___x_1568_);
v___x_1570_ = lean_nat_dec_le(v___x_1567_, v___x_1569_);
lean_dec(v___x_1569_);
lean_dec(v___x_1567_);
if (v___x_1570_ == 0)
{
lean_dec(v___x_1563_);
lean_dec(v_index_1559_);
goto v___jp_1545_;
}
else
{
lean_object* v___x_1571_; 
lean_inc(v_declName_1426_);
v___x_1571_ = l_Std_DHashMap_Raw_setEntry___redArg(v_keys_1476_, v___x_1563_, v_index_1559_, v_declName_1426_, v_keys_1427_);
lean_dec(v_index_1559_);
v___y_1490_ = v___x_1571_;
goto v___jp_1489_;
}
}
}
default: 
{
lean_object* v_size_1572_; lean_object* v_keyArray_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_size_1572_ = lean_ctor_get(v_keys_1476_, 0);
v_keyArray_1573_ = lean_ctor_get(v_keys_1476_, 1);
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_size_1572_, v___x_1574_);
v___x_1576_ = lean_array_get_size(v_keyArray_1573_);
v___x_1577_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec(v___x_1575_);
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_keys_1476_);
lean_dec_ref(v_keys_1476_);
v___y_1529_ = v___x_1578_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1579_ = lean_unsigned_to_nat(4u);
v___x_1580_ = lean_nat_mul(v___x_1575_, v___x_1579_);
lean_dec(v___x_1575_);
v___x_1581_ = lean_unsigned_to_nat(3u);
v___x_1582_ = lean_nat_mul(v___x_1576_, v___x_1581_);
v___x_1583_ = lean_nat_dec_le(v___x_1580_, v___x_1582_);
lean_dec(v___x_1582_);
lean_dec(v___x_1580_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_keys_1476_);
lean_dec_ref(v_keys_1476_);
v___y_1529_ = v___x_1584_;
goto v___jp_1528_;
}
else
{
v___y_1529_ = v_keys_1476_;
goto v___jp_1528_;
}
}
}
}
v___jp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___y_1443_);
lean_ctor_set(v___x_1437_, 0, v___y_1442_);
v___x_1445_ = v___x_1437_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___y_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___y_1443_);
v___x_1445_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_st_ref_put(v___x_1433_, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
}
v___jp_1449_:
{
lean_object* v_size_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_size_1453_ = lean_ctor_get(v___y_1451_, 0);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_size_1453_, v___x_1454_);
v___x_1456_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1451_, v___x_1455_, v_i_1452_, v_declName_1426_, v_proc_1428_);
lean_dec(v_i_1452_);
v___y_1442_ = v___y_1450_;
v___y_1443_ = v___x_1456_;
goto v___jp_1441_;
}
v___jp_1457_:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v___y_1459_, v_declName_1426_);
switch(lean_obj_tag(v___x_1460_))
{
case 0:
{
lean_object* v_index_1461_; lean_object* v_size_1462_; lean_object* v___x_1463_; 
v_index_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_index_1461_);
lean_dec_ref_known(v___x_1460_, 3);
v_size_1462_ = lean_ctor_get(v___y_1459_, 0);
lean_inc(v_size_1462_);
v___x_1463_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1459_, v_size_1462_, v_index_1461_, v_declName_1426_, v_proc_1428_);
lean_dec(v_index_1461_);
v___y_1442_ = v___y_1458_;
v___y_1443_ = v___x_1463_;
goto v___jp_1441_;
}
case 1:
{
lean_object* v_index_1464_; 
v_index_1464_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_index_1464_);
lean_dec_ref_known(v___x_1460_, 1);
v___y_1450_ = v___y_1458_;
v___y_1451_ = v___y_1459_;
v_i_1452_ = v_index_1464_;
goto v___jp_1449_;
}
default: 
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1459_, v___x_1465_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_index_1467_; 
v_index_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_index_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___y_1450_ = v___y_1458_;
v___y_1451_ = v___y_1459_;
v_i_1452_ = v_index_1467_;
goto v___jp_1449_;
}
else
{
lean_dec_ref(v_proc_1428_);
lean_dec(v_declName_1426_);
v___y_1442_ = v___y_1458_;
v___y_1443_ = v___y_1459_;
goto v___jp_1441_;
}
}
}
}
v___jp_1468_:
{
lean_object* v_size_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_size_1472_ = lean_ctor_get(v___y_1469_, 0);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_size_1472_, v___x_1473_);
v___x_1475_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1469_, v___x_1474_, v_i_1471_, v_declName_1426_, v_proc_1428_);
lean_dec(v_i_1471_);
v___y_1442_ = v___y_1470_;
v___y_1443_ = v___x_1475_;
goto v___jp_1441_;
}
v___jp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_procs_1477_);
lean_dec_ref(v_procs_1477_);
v___x_1481_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v___x_1480_, v_declName_1426_);
switch(lean_obj_tag(v___x_1481_))
{
case 0:
{
lean_object* v_index_1482_; lean_object* v_size_1483_; lean_object* v___x_1484_; 
v_index_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_index_1482_);
lean_dec_ref_known(v___x_1481_, 3);
v_size_1483_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_size_1483_);
v___x_1484_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1480_, v_size_1483_, v_index_1482_, v_declName_1426_, v_proc_1428_);
lean_dec(v_index_1482_);
v___y_1442_ = v___y_1479_;
v___y_1443_ = v___x_1484_;
goto v___jp_1441_;
}
case 1:
{
lean_object* v_index_1485_; 
v_index_1485_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_index_1485_);
lean_dec_ref_known(v___x_1481_, 1);
v___y_1469_ = v___x_1480_;
v___y_1470_ = v___y_1479_;
v_i_1471_ = v_index_1485_;
goto v___jp_1468_;
}
default: 
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1480_, v___x_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_index_1488_; 
v_index_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_index_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___y_1469_ = v___x_1480_;
v___y_1470_ = v___y_1479_;
v_i_1471_ = v_index_1488_;
goto v___jp_1468_;
}
else
{
lean_dec_ref(v_proc_1428_);
lean_dec(v_declName_1426_);
v___y_1442_ = v___y_1479_;
v___y_1443_ = v___x_1480_;
goto v___jp_1441_;
}
}
}
}
v___jp_1489_:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_1477_, v_declName_1426_);
switch(lean_obj_tag(v___x_1491_))
{
case 0:
{
lean_object* v_index_1492_; lean_object* v_size_1493_; lean_object* v___x_1494_; 
v_index_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_index_1492_);
lean_dec_ref_known(v___x_1491_, 3);
v_size_1493_ = lean_ctor_get(v_procs_1477_, 0);
lean_inc(v_size_1493_);
v___x_1494_ = l_Std_DHashMap_Raw_setEntry___redArg(v_procs_1477_, v_size_1493_, v_index_1492_, v_declName_1426_, v_proc_1428_);
lean_dec(v_index_1492_);
v___y_1442_ = v___y_1490_;
v___y_1443_ = v___x_1494_;
goto v___jp_1441_;
}
case 1:
{
lean_object* v_index_1495_; lean_object* v_size_1496_; lean_object* v_keyArray_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_index_1495_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_index_1495_);
lean_dec_ref_known(v___x_1491_, 1);
v_size_1496_ = lean_ctor_get(v_procs_1477_, 0);
v_keyArray_1497_ = lean_ctor_get(v_procs_1477_, 1);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v_size_1496_, v___x_1498_);
v___x_1500_ = lean_array_get_size(v_keyArray_1497_);
v___x_1501_ = lean_nat_dec_lt(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec(v___x_1499_);
lean_dec(v_index_1495_);
v___y_1479_ = v___y_1490_;
goto v___jp_1478_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1502_ = lean_unsigned_to_nat(4u);
v___x_1503_ = lean_nat_mul(v___x_1499_, v___x_1502_);
v___x_1504_ = lean_unsigned_to_nat(3u);
v___x_1505_ = lean_nat_mul(v___x_1500_, v___x_1504_);
v___x_1506_ = lean_nat_dec_le(v___x_1503_, v___x_1505_);
lean_dec(v___x_1505_);
lean_dec(v___x_1503_);
if (v___x_1506_ == 0)
{
lean_dec(v___x_1499_);
lean_dec(v_index_1495_);
v___y_1479_ = v___y_1490_;
goto v___jp_1478_;
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Std_DHashMap_Raw_setEntry___redArg(v_procs_1477_, v___x_1499_, v_index_1495_, v_declName_1426_, v_proc_1428_);
lean_dec(v_index_1495_);
v___y_1442_ = v___y_1490_;
v___y_1443_ = v___x_1507_;
goto v___jp_1441_;
}
}
}
default: 
{
lean_object* v_size_1508_; lean_object* v_keyArray_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_size_1508_ = lean_ctor_get(v_procs_1477_, 0);
v_keyArray_1509_ = lean_ctor_get(v_procs_1477_, 1);
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_nat_add(v_size_1508_, v___x_1510_);
v___x_1512_ = lean_array_get_size(v_keyArray_1509_);
v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
lean_dec(v___x_1511_);
v___x_1514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_procs_1477_);
lean_dec_ref(v_procs_1477_);
v___y_1458_ = v___y_1490_;
v___y_1459_ = v___x_1514_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1515_ = lean_unsigned_to_nat(4u);
v___x_1516_ = lean_nat_mul(v___x_1511_, v___x_1515_);
lean_dec(v___x_1511_);
v___x_1517_ = lean_unsigned_to_nat(3u);
v___x_1518_ = lean_nat_mul(v___x_1512_, v___x_1517_);
v___x_1519_ = lean_nat_dec_le(v___x_1516_, v___x_1518_);
lean_dec(v___x_1518_);
lean_dec(v___x_1516_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_procs_1477_);
lean_dec_ref(v_procs_1477_);
v___y_1458_ = v___y_1490_;
v___y_1459_ = v___x_1520_;
goto v___jp_1457_;
}
else
{
v___y_1458_ = v___y_1490_;
v___y_1459_ = v_procs_1477_;
goto v___jp_1457_;
}
}
}
}
}
v___jp_1521_:
{
lean_object* v_size_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_size_1524_ = lean_ctor_get(v___y_1522_, 0);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_size_1524_, v___x_1525_);
lean_inc(v_declName_1426_);
v___x_1527_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1522_, v___x_1526_, v_i_1523_, v_declName_1426_, v_keys_1427_);
lean_dec(v_i_1523_);
v___y_1490_ = v___x_1527_;
goto v___jp_1489_;
}
v___jp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v___y_1529_, v_declName_1426_);
switch(lean_obj_tag(v___x_1530_))
{
case 0:
{
lean_object* v_index_1531_; lean_object* v_size_1532_; lean_object* v___x_1533_; 
v_index_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_index_1531_);
lean_dec_ref_known(v___x_1530_, 3);
v_size_1532_ = lean_ctor_get(v___y_1529_, 0);
lean_inc(v_size_1532_);
lean_inc(v_declName_1426_);
v___x_1533_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1529_, v_size_1532_, v_index_1531_, v_declName_1426_, v_keys_1427_);
lean_dec(v_index_1531_);
v___y_1490_ = v___x_1533_;
goto v___jp_1489_;
}
case 1:
{
lean_object* v_index_1534_; 
v_index_1534_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_index_1534_);
lean_dec_ref_known(v___x_1530_, 1);
v___y_1522_ = v___y_1529_;
v_i_1523_ = v_index_1534_;
goto v___jp_1521_;
}
default: 
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1529_, v___x_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_index_1537_; 
v_index_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_index_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___y_1522_ = v___y_1529_;
v_i_1523_ = v_index_1537_;
goto v___jp_1521_;
}
else
{
lean_dec_ref(v_keys_1427_);
v___y_1490_ = v___y_1529_;
goto v___jp_1489_;
}
}
}
}
v___jp_1538_:
{
lean_object* v_size_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_size_1541_ = lean_ctor_get(v___y_1539_, 0);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_add(v_size_1541_, v___x_1542_);
lean_inc(v_declName_1426_);
v___x_1544_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1539_, v___x_1543_, v_i_1540_, v_declName_1426_, v_keys_1427_);
lean_dec(v_i_1540_);
v___y_1490_ = v___x_1544_;
goto v___jp_1489_;
}
v___jp_1545_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_keys_1476_);
lean_dec_ref(v_keys_1476_);
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v___x_1546_, v_declName_1426_);
switch(lean_obj_tag(v___x_1547_))
{
case 0:
{
lean_object* v_index_1548_; lean_object* v_size_1549_; lean_object* v___x_1550_; 
v_index_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_index_1548_);
lean_dec_ref_known(v___x_1547_, 3);
v_size_1549_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_size_1549_);
lean_inc(v_declName_1426_);
v___x_1550_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1546_, v_size_1549_, v_index_1548_, v_declName_1426_, v_keys_1427_);
lean_dec(v_index_1548_);
v___y_1490_ = v___x_1550_;
goto v___jp_1489_;
}
case 1:
{
lean_object* v_index_1551_; 
v_index_1551_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_index_1551_);
lean_dec_ref_known(v___x_1547_, 1);
v___y_1539_ = v___x_1546_;
v_i_1540_ = v_index_1551_;
goto v___jp_1538_;
}
default: 
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1546_, v___x_1552_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_index_1554_; 
v_index_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_index_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___y_1539_ = v___x_1546_;
v_i_1540_ = v_index_1554_;
goto v___jp_1538_;
}
else
{
lean_dec_ref(v_keys_1427_);
v___y_1490_ = v___x_1546_;
goto v___jp_1489_;
}
}
}
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_del_object(v___x_1437_);
lean_dec_ref(v_proc_1428_);
lean_dec_ref(v_keys_1427_);
v___x_1585_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2));
v___x_1586_ = l_Lean_privateToUserName(v_declName_1426_);
v___x_1587_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1586_, v___x_1439_);
v___x_1588_ = lean_string_append(v___x_1585_, v___x_1587_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_1590_ = lean_string_append(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_mk_io_user_error(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object* v_declName_1595_, lean_object* v_keys_1596_, lean_object* v_proc_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1595_, v_keys_1596_, v_proc_1597_);
return v_res_1599_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object* v_00_u03b2_1600_, lean_object* v_m_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1601_, v_a_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object* v_00_u03b2_1604_, lean_object* v_m_1605_, lean_object* v_a_1606_){
_start:
{
uint8_t v_res_1607_; lean_object* v_r_1608_; 
v_res_1607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_1604_, v_m_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_m_1605_);
v_r_1608_ = lean_box(v_res_1607_);
return v_r_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object* v_00_u03b2_1609_, lean_object* v_m_1610_, lean_object* v_query_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1610_, v_query_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___boxed(lean_object* v_00_u03b2_1613_, lean_object* v_m_1614_, lean_object* v_query_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(v_00_u03b2_1613_, v_m_1614_, v_query_1615_);
lean_dec(v_query_1615_);
lean_dec_ref(v_m_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2(lean_object* v_00_u03b2_1617_, lean_object* v_m_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___redArg(v_m_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2___boxed(lean_object* v_00_u03b2_1620_, lean_object* v_m_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2(v_00_u03b2_1620_, v_m_1621_);
lean_dec_ref(v_m_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object* v_00_u03b2_1623_, lean_object* v_m_1624_, lean_object* v_query_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_m_1624_, v_query_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1627_, lean_object* v_m_1628_, lean_object* v_query_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_1627_, v_m_1628_, v_query_1629_);
lean_dec(v_query_1629_);
lean_dec_ref(v_m_1628_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object* v_00_u03b2_1631_, lean_object* v_m_1632_, lean_object* v_query_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_m_1632_, v_query_1633_, v_x_1634_, v_x_1635_, v_x_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1639_, lean_object* v_m_1640_, lean_object* v_query_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(v_00_u03b2_1639_, v_m_1640_, v_query_1641_, v_x_1642_, v_x_1643_, v_x_1644_, v_x_1645_);
lean_dec(v_query_1641_);
lean_dec_ref(v_m_1640_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4(lean_object* v_00_u03b2_1647_, lean_object* v_init_1648_, lean_object* v_b_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___redArg(v_init_1648_, v_b_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_init_1652_, lean_object* v_b_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4(v_00_u03b2_1651_, v_init_1652_, v_b_1653_);
lean_dec_ref(v_b_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1655_, lean_object* v_b_1656_, lean_object* v_acc_1657_, lean_object* v_i_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___redArg(v_b_1656_, v_acc_1657_, v_i_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1660_, lean_object* v_b_1661_, lean_object* v_acc_1662_, lean_object* v_i_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__2_spec__4_spec__5(v_00_u03b2_1660_, v_b_1661_, v_acc_1662_, v_i_1663_);
lean_dec_ref(v_b_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object* v_d_u2081_1672_, lean_object* v_d_u2082_1673_){
_start:
{
lean_object* v_declName_1674_; lean_object* v_declName_1675_; uint8_t v___x_1676_; 
v_declName_1674_ = lean_ctor_get(v_d_u2081_1672_, 0);
v_declName_1675_ = lean_ctor_get(v_d_u2082_1673_, 0);
v___x_1676_ = l_Lean_Name_quickLt(v_declName_1674_, v_declName_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object* v_d_u2081_1677_, lean_object* v_d_u2082_1678_){
_start:
{
uint8_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1677_, v_d_u2082_1678_);
lean_dec_ref(v_d_u2082_1678_);
lean_dec_ref(v_d_u2081_1677_);
v_r_1680_ = lean_box(v_res_1679_);
return v_r_1680_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
v___x_1685_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_s_1689_, lean_object* v_d_1690_){
_start:
{
lean_object* v_builtin_1691_; lean_object* v_newEntries_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1702_; 
v_builtin_1691_ = lean_ctor_get(v_s_1689_, 0);
v_newEntries_1692_ = lean_ctor_get(v_s_1689_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_s_1689_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1694_ = v_s_1689_;
v_isShared_1695_ = v_isSharedCheck_1702_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_newEntries_1692_);
lean_inc(v_builtin_1691_);
lean_dec(v_s_1689_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1702_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_declName_1696_; lean_object* v_keys_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v_declName_1696_ = lean_ctor_get(v_d_1690_, 0);
lean_inc(v_declName_1696_);
v_keys_1697_ = lean_ctor_get(v_d_1690_, 1);
lean_inc_ref(v_keys_1697_);
lean_dec_ref(v_d_1690_);
v___x_1698_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_1692_, v_declName_1696_, v_keys_1697_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1698_);
v___x_1700_ = v___x_1694_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_builtin_1691_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_result_1703_, lean_object* v_declName_1704_, lean_object* v_keys_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_declName_1704_);
lean_ctor_set(v___x_1706_, 1, v_keys_1705_);
v___x_1707_ = lean_array_push(v_result_1703_, v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_1708_, lean_object* v_x1_1709_, lean_object* v_x2_1710_, lean_object* v_x3_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_apply_3(v_f_1708_, v_x1_1709_, v_x2_1710_, v_x3_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_1713_, lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_i_1716_, lean_object* v_acc_1717_){
_start:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_array_get_size(v_keys_1714_);
v___x_1719_ = lean_nat_dec_lt(v_i_1716_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec(v_i_1716_);
lean_dec(v_f_1713_);
return v_acc_1717_;
}
else
{
lean_object* v_k_1720_; lean_object* v_v_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_k_1720_ = lean_array_fget_borrowed(v_keys_1714_, v_i_1716_);
v_v_1721_ = lean_array_fget_borrowed(v_vals_1715_, v_i_1716_);
lean_inc(v_f_1713_);
lean_inc(v_v_1721_);
lean_inc(v_k_1720_);
v___x_1722_ = lean_apply_3(v_f_1713_, v_acc_1717_, v_k_1720_, v_v_1721_);
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_nat_add(v_i_1716_, v___x_1723_);
lean_dec(v_i_1716_);
v_i_1716_ = v___x_1724_;
v_acc_1717_ = v___x_1722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_1726_, lean_object* v_keys_1727_, lean_object* v_vals_1728_, lean_object* v_i_1729_, lean_object* v_acc_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1726_, v_keys_1727_, v_vals_1728_, v_i_1729_, v_acc_1730_);
lean_dec_ref(v_vals_1728_);
lean_dec_ref(v_keys_1727_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_object* v_es_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_es_1735_ = lean_ctor_get(v_x_1733_, 0);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_array_get_size(v_es_1735_);
v___x_1738_ = lean_nat_dec_lt(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_dec(v_f_1732_);
return v_x_1734_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_nat_dec_le(v___x_1737_, v___x_1737_);
if (v___x_1739_ == 0)
{
if (v___x_1738_ == 0)
{
lean_dec(v_f_1732_);
return v_x_1734_;
}
else
{
size_t v___x_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = lean_usize_of_nat(v___x_1737_);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1732_, v_es_1735_, v___x_1740_, v___x_1741_, v_x_1734_);
return v___x_1742_;
}
}
else
{
size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = lean_usize_of_nat(v___x_1737_);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1732_, v_es_1735_, v___x_1743_, v___x_1744_, v_x_1734_);
return v___x_1745_;
}
}
}
else
{
lean_object* v_ks_1746_; lean_object* v_vs_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_ks_1746_ = lean_ctor_get(v_x_1733_, 0);
v_vs_1747_ = lean_ctor_get(v_x_1733_, 1);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1732_, v_ks_1746_, v_vs_1747_, v___x_1748_, v_x_1734_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1750_, lean_object* v_as_1751_, size_t v_i_1752_, size_t v_stop_1753_, lean_object* v_b_1754_){
_start:
{
lean_object* v___y_1756_; uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_eq(v_i_1752_, v_stop_1753_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_array_uget_borrowed(v_as_1751_, v_i_1752_);
switch(lean_obj_tag(v___x_1761_))
{
case 0:
{
lean_object* v_key_1762_; lean_object* v_val_1763_; lean_object* v___x_1764_; 
v_key_1762_ = lean_ctor_get(v___x_1761_, 0);
v_val_1763_ = lean_ctor_get(v___x_1761_, 1);
lean_inc(v_f_1750_);
lean_inc(v_val_1763_);
lean_inc(v_key_1762_);
v___x_1764_ = lean_apply_3(v_f_1750_, v_b_1754_, v_key_1762_, v_val_1763_);
v___y_1756_ = v___x_1764_;
goto v___jp_1755_;
}
case 1:
{
lean_object* v_node_1765_; lean_object* v___x_1766_; 
v_node_1765_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_f_1750_);
v___x_1766_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1750_, v_node_1765_, v_b_1754_);
v___y_1756_ = v___x_1766_;
goto v___jp_1755_;
}
default: 
{
v___y_1756_ = v_b_1754_;
goto v___jp_1755_;
}
}
}
else
{
lean_dec(v_f_1750_);
return v_b_1754_;
}
v___jp_1755_:
{
size_t v___x_1757_; size_t v___x_1758_; 
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1752_, v___x_1757_);
v_i_1752_ = v___x_1758_;
v_b_1754_ = v___y_1756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1767_, lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_){
_start:
{
size_t v_i_boxed_1772_; size_t v_stop_boxed_1773_; lean_object* v_res_1774_; 
v_i_boxed_1772_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1773_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1767_, v_as_1768_, v_i_boxed_1772_, v_stop_boxed_1773_, v_b_1771_);
lean_dec_ref(v_as_1768_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1775_, v_x_1776_, v_x_1777_);
lean_dec_ref(v_x_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_1779_, lean_object* v_f_1780_, lean_object* v_init_1781_){
_start:
{
lean_object* v___f_1782_; lean_object* v___x_1783_; 
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1782_, 0, v_f_1780_);
v___x_1783_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1782_, v_map_1779_, v_init_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_1784_, lean_object* v_f_1785_, lean_object* v_init_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1784_, v_f_1785_, v_init_1786_);
lean_dec_ref(v_map_1784_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_1788_, lean_object* v_pivot_1789_, lean_object* v_as_1790_, lean_object* v_i_1791_, lean_object* v_k_1792_){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_nat_dec_lt(v_k_1792_, v_hi_1788_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec(v_k_1792_);
v___x_1794_ = lean_array_fswap(v_as_1790_, v_i_1791_, v_hi_1788_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_i_1791_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_array_fget_borrowed(v_as_1790_, v_k_1792_);
v___x_1797_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1796_, v_pivot_1789_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_add(v_k_1792_, v___x_1798_);
lean_dec(v_k_1792_);
v_k_1792_ = v___x_1799_;
goto _start;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_array_fswap(v_as_1790_, v_i_1791_, v_k_1792_);
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_nat_add(v_i_1791_, v___x_1802_);
lean_dec(v_i_1791_);
v___x_1804_ = lean_nat_add(v_k_1792_, v___x_1802_);
lean_dec(v_k_1792_);
v_as_1790_ = v___x_1801_;
v_i_1791_ = v___x_1803_;
v_k_1792_ = v___x_1804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_1806_, lean_object* v_pivot_1807_, lean_object* v_as_1808_, lean_object* v_i_1809_, lean_object* v_k_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1806_, v_pivot_1807_, v_as_1808_, v_i_1809_, v_k_1810_);
lean_dec_ref(v_pivot_1807_);
lean_dec(v_hi_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_1812_, lean_object* v_as_1813_, lean_object* v_lo_1814_, lean_object* v_hi_1815_){
_start:
{
lean_object* v___y_1817_; uint8_t v___x_1827_; 
v___x_1827_ = lean_nat_dec_lt(v_lo_1814_, v_hi_1815_);
if (v___x_1827_ == 0)
{
lean_dec(v_lo_1814_);
return v_as_1813_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_mid_1830_; lean_object* v___y_1832_; lean_object* v___y_1838_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1828_ = lean_nat_add(v_lo_1814_, v_hi_1815_);
v___x_1829_ = lean_unsigned_to_nat(1u);
v_mid_1830_ = lean_nat_shiftr(v___x_1828_, v___x_1829_);
lean_dec(v___x_1828_);
v___x_1843_ = lean_array_fget_borrowed(v_as_1813_, v_mid_1830_);
v___x_1844_ = lean_array_fget_borrowed(v_as_1813_, v_lo_1814_);
v___x_1845_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
v___y_1838_ = v_as_1813_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_array_fswap(v_as_1813_, v_lo_1814_, v_mid_1830_);
v___y_1838_ = v___x_1846_;
goto v___jp_1837_;
}
v___jp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = lean_array_fget_borrowed(v___y_1832_, v_mid_1830_);
v___x_1834_ = lean_array_fget_borrowed(v___y_1832_, v_hi_1815_);
v___x_1835_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_dec(v_mid_1830_);
v___y_1817_ = v___y_1832_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_array_fswap(v___y_1832_, v_mid_1830_, v_hi_1815_);
lean_dec(v_mid_1830_);
v___y_1817_ = v___x_1836_;
goto v___jp_1816_;
}
}
v___jp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_array_fget_borrowed(v___y_1838_, v_hi_1815_);
v___x_1840_ = lean_array_fget_borrowed(v___y_1838_, v_lo_1814_);
v___x_1841_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
v___y_1832_ = v___y_1838_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_array_fswap(v___y_1838_, v_lo_1814_, v_hi_1815_);
v___y_1832_ = v___x_1842_;
goto v___jp_1831_;
}
}
}
v___jp_1816_:
{
lean_object* v_pivot_1818_; lean_object* v___x_1819_; lean_object* v_fst_1820_; lean_object* v_snd_1821_; uint8_t v___x_1822_; 
v_pivot_1818_ = lean_array_fget(v___y_1817_, v_hi_1815_);
lean_inc_n(v_lo_1814_, 2);
v___x_1819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1815_, v_pivot_1818_, v___y_1817_, v_lo_1814_, v_lo_1814_);
lean_dec(v_pivot_1818_);
v_fst_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_fst_1820_);
v_snd_1821_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_snd_1821_);
lean_dec_ref(v___x_1819_);
v___x_1822_ = lean_nat_dec_le(v_hi_1815_, v_fst_1820_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1812_, v_snd_1821_, v_lo_1814_, v_fst_1820_);
v___x_1824_ = lean_unsigned_to_nat(1u);
v___x_1825_ = lean_nat_add(v_fst_1820_, v___x_1824_);
lean_dec(v_fst_1820_);
v_as_1813_ = v___x_1823_;
v_lo_1814_ = v___x_1825_;
goto _start;
}
else
{
lean_dec(v_fst_1820_);
lean_dec(v_lo_1814_);
return v_snd_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_1847_, lean_object* v_as_1848_, lean_object* v_lo_1849_, lean_object* v_hi_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1847_, v_as_1848_, v_lo_1849_, v_hi_1850_);
lean_dec(v_hi_1850_);
lean_dec(v_n_1847_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1854_, lean_object* v_s_1855_){
_start:
{
lean_object* v_newEntries_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v_result_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_newEntries_1856_ = lean_ctor_get(v_s_1855_, 1);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1859_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1856_, v___f_1854_, v___x_1858_);
v___x_1860_ = lean_array_get_size(v_result_1859_);
v___x_1861_ = lean_nat_dec_eq(v___x_1860_, v___x_1857_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___y_1865_; uint8_t v___x_1869_; 
v___x_1862_ = lean_unsigned_to_nat(1u);
v___x_1863_ = lean_nat_sub(v___x_1860_, v___x_1862_);
v___x_1869_ = lean_nat_dec_le(v___x_1857_, v___x_1863_);
if (v___x_1869_ == 0)
{
lean_inc(v___x_1863_);
v___y_1865_ = v___x_1863_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___x_1857_;
goto v___jp_1864_;
}
v___jp_1864_:
{
uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_le(v___y_1865_, v___x_1863_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec(v___x_1863_);
lean_inc(v___y_1865_);
v___x_1867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1860_, v_result_1859_, v___y_1865_, v___y_1865_);
lean_dec(v___y_1865_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; 
v___x_1868_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1860_, v_result_1859_, v___y_1865_, v___x_1863_);
lean_dec(v___x_1863_);
return v___x_1868_;
}
}
}
else
{
return v_result_1859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1870_, lean_object* v_s_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1870_, v_s_1871_);
lean_dec_ref(v_s_1871_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_box(0);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_x_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_1875_);
lean_dec_ref(v_x_1875_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1877_, lean_object* v_x_1878_, lean_object* v_s_1879_){
_start:
{
lean_object* v_newEntries_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_result_1883_; lean_object* v___x_1884_; lean_object* v___y_1886_; lean_object* v___y_1887_; uint8_t v___x_1890_; 
v_newEntries_1880_ = lean_ctor_get(v_s_1879_, 1);
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1883_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1880_, v___f_1877_, v___x_1882_);
v___x_1884_ = lean_array_get_size(v_result_1883_);
v___x_1890_ = lean_nat_dec_eq(v___x_1884_, v___x_1881_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___y_1894_; uint8_t v___x_1896_; 
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_sub(v___x_1884_, v___x_1891_);
v___x_1896_ = lean_nat_dec_le(v___x_1881_, v___x_1892_);
if (v___x_1896_ == 0)
{
lean_inc(v___x_1892_);
v___y_1894_ = v___x_1892_;
goto v___jp_1893_;
}
else
{
v___y_1894_ = v___x_1881_;
goto v___jp_1893_;
}
v___jp_1893_:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_nat_dec_le(v___y_1894_, v___x_1892_);
if (v___x_1895_ == 0)
{
lean_dec(v___x_1892_);
lean_inc(v___y_1894_);
v___y_1886_ = v___y_1894_;
v___y_1887_ = v___y_1894_;
goto v___jp_1885_;
}
else
{
v___y_1886_ = v___y_1894_;
v___y_1887_ = v___x_1892_;
goto v___jp_1885_;
}
}
}
else
{
lean_object* v___x_1897_; 
lean_inc_n(v_result_1883_, 2);
v___x_1897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1897_, 0, v_result_1883_);
lean_ctor_set(v___x_1897_, 1, v_result_1883_);
lean_ctor_set(v___x_1897_, 2, v_result_1883_);
return v___x_1897_;
}
v___jp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1884_, v_result_1883_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_inc_ref_n(v___x_1888_, 2);
v___x_1889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
lean_ctor_set(v___x_1889_, 2, v___x_1888_);
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1898_, lean_object* v_x_1899_, lean_object* v_s_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1898_, v_x_1899_, v_s_1900_);
lean_dec_ref(v_s_1900_);
lean_dec_ref(v_x_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v_keys_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1914_; 
v___x_1904_ = lean_st_ref_get(v___x_1902_);
v_keys_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v___x_1904_, 1);
lean_dec(v_unused_1915_);
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_keys_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_keys_1905_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1916_);
lean_dec(v___x_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_keys_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1933_; 
v___x_1923_ = lean_st_ref_get(v___x_1919_);
v_keys_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v___x_1923_, 1);
lean_dec(v_unused_1934_);
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_keys_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_keys_1924_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1935_, v_x_1936_, v___y_1937_);
lean_dec_ref(v___y_1937_);
lean_dec_ref(v_x_1936_);
lean_dec(v___x_1935_);
return v_res_1939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___f_1955_; 
v___x_1954_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1955_, 0, v___x_1954_);
return v___f_1955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___f_1957_; 
v___x_1956_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_1957_, 0, v___x_1956_);
return v___f_1957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___f_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_box(2);
v___f_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___f_1964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1966_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___f_1964_);
lean_ctor_set(v___x_1966_, 2, v___f_1963_);
lean_ctor_set(v___x_1966_, 3, v___f_1962_);
lean_ctor_set(v___x_1966_, 4, v___f_1961_);
lean_ctor_set(v___x_1966_, 5, v___f_1960_);
lean_ctor_set(v___x_1966_, 6, v___x_1959_);
lean_ctor_set(v___x_1966_, 7, v___x_1958_);
return v___x_1966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___f_1967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v___f_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1972_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_map_1977_, lean_object* v_f_1978_, lean_object* v_init_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1977_, v_f_1978_, v_init_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_map_1983_, lean_object* v_f_1984_, lean_object* v_init_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_1981_, v_00_u03b2_1982_, v_map_1983_, v_f_1984_, v_init_1985_);
lean_dec_ref(v_map_1983_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object* v_n_1987_, lean_object* v_as_1988_, lean_object* v_lo_1989_, lean_object* v_hi_1990_, lean_object* v_w_1991_, lean_object* v_hlo_1992_, lean_object* v_hhi_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1987_, v_as_1988_, v_lo_1989_, v_hi_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1995_, lean_object* v_as_1996_, lean_object* v_lo_1997_, lean_object* v_hi_1998_, lean_object* v_w_1999_, lean_object* v_hlo_2000_, lean_object* v_hhi_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_1995_, v_as_1996_, v_lo_1997_, v_hi_1998_, v_w_1999_, v_hlo_2000_, v_hhi_2001_);
lean_dec(v_hi_1998_);
lean_dec(v_n_1995_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_2003_, lean_object* v_f_2004_, lean_object* v_init_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_2004_, v_map_2003_, v_init_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_2007_, lean_object* v_f_2008_, lean_object* v_init_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_2007_, v_f_2008_, v_init_2009_);
lean_dec_ref(v_map_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_2011_, lean_object* v_00_u03b2_2012_, lean_object* v_map_2013_, lean_object* v_f_2014_, lean_object* v_init_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_2014_, v_map_2013_, v_init_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_map_2019_, lean_object* v_f_2020_, lean_object* v_init_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_2017_, v_00_u03b2_2018_, v_map_2019_, v_f_2020_, v_init_2021_);
lean_dec_ref(v_map_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_2023_, lean_object* v_lo_2024_, lean_object* v_hi_2025_, lean_object* v_hhi_2026_, lean_object* v_pivot_2027_, lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_k_2030_, lean_object* v_ilo_2031_, lean_object* v_ik_2032_, lean_object* v_w_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2025_, v_pivot_2027_, v_as_2028_, v_i_2029_, v_k_2030_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_2035_, lean_object* v_lo_2036_, lean_object* v_hi_2037_, lean_object* v_hhi_2038_, lean_object* v_pivot_2039_, lean_object* v_as_2040_, lean_object* v_i_2041_, lean_object* v_k_2042_, lean_object* v_ilo_2043_, lean_object* v_ik_2044_, lean_object* v_w_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(v_n_2035_, v_lo_2036_, v_hi_2037_, v_hhi_2038_, v_pivot_2039_, v_as_2040_, v_i_2041_, v_k_2042_, v_ilo_2043_, v_ik_2044_, v_w_2045_);
lean_dec_ref(v_pivot_2039_);
lean_dec(v_hi_2037_);
lean_dec(v_lo_2036_);
lean_dec(v_n_2035_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2047_, lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_f_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_2050_, v_x_2051_, v_x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2054_, lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_f_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_2054_, v_00_u03b1_2055_, v_00_u03b2_2056_, v_f_2057_, v_x_2058_, v_x_2059_);
lean_dec_ref(v_x_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_00_u03c3_2063_, lean_object* v_f_2064_, lean_object* v_as_2065_, size_t v_i_2066_, size_t v_stop_2067_, lean_object* v_b_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_2064_, v_as_2065_, v_i_2066_, v_stop_2067_, v_b_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_00_u03c3_2072_, lean_object* v_f_2073_, lean_object* v_as_2074_, lean_object* v_i_2075_, lean_object* v_stop_2076_, lean_object* v_b_2077_){
_start:
{
size_t v_i_boxed_2078_; size_t v_stop_boxed_2079_; lean_object* v_res_2080_; 
v_i_boxed_2078_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_stop_boxed_2079_ = lean_unbox_usize(v_stop_2076_);
lean_dec(v_stop_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2070_, v_00_u03b2_2071_, v_00_u03c3_2072_, v_f_2073_, v_as_2074_, v_i_boxed_2078_, v_stop_boxed_2079_, v_b_2077_);
lean_dec_ref(v_as_2074_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_2081_, lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_f_2084_, lean_object* v_keys_2085_, lean_object* v_vals_2086_, lean_object* v_heq_2087_, lean_object* v_i_2088_, lean_object* v_acc_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_2084_, v_keys_2085_, v_vals_2086_, v_i_2088_, v_acc_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_2091_, lean_object* v_00_u03b1_2092_, lean_object* v_00_u03b2_2093_, lean_object* v_f_2094_, lean_object* v_keys_2095_, lean_object* v_vals_2096_, lean_object* v_heq_2097_, lean_object* v_i_2098_, lean_object* v_acc_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_2091_, v_00_u03b1_2092_, v_00_u03b2_2093_, v_f_2094_, v_keys_2095_, v_vals_2096_, v_heq_2097_, v_i_2098_, v_acc_2099_);
lean_dec_ref(v_vals_2096_);
lean_dec_ref(v_keys_2095_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_m_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_value_2104_; lean_object* v___x_2105_; 
v_value_2104_ = lean_ctor_get(v___x_2103_, 2);
lean_inc(v_value_2104_);
lean_dec_ref_known(v___x_2103_, 3);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_value_2104_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_box(0);
return v___x_2106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_m_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_2110_, lean_object* v_k_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_m_2116_; lean_object* v_a_2117_; uint8_t v___x_2118_; 
v___x_2114_ = lean_nat_add(v_x_2112_, v_x_2113_);
v___x_2115_ = lean_unsigned_to_nat(1u);
v_m_2116_ = lean_nat_shiftr(v___x_2114_, v___x_2115_);
lean_dec(v___x_2114_);
v_a_2117_ = lean_array_fget_borrowed(v_as_2110_, v_m_2116_);
v___x_2118_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_2117_, v_k_2111_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; 
lean_dec(v_x_2113_);
v___x_2119_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_2111_, v_a_2117_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec(v_m_2116_);
lean_dec(v_x_2112_);
lean_inc(v_a_2117_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_a_2117_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = lean_nat_dec_eq(v_m_2116_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = lean_nat_sub(v_m_2116_, v___x_2115_);
lean_dec(v_m_2116_);
v___x_2124_ = lean_nat_dec_lt(v___x_2123_, v_x_2112_);
if (v___x_2124_ == 0)
{
v_x_2113_ = v___x_2123_;
goto _start;
}
else
{
lean_object* v___x_2126_; 
lean_dec(v___x_2123_);
lean_dec(v_x_2112_);
v___x_2126_ = lean_box(0);
return v___x_2126_;
}
}
else
{
lean_object* v___x_2127_; 
lean_dec(v_m_2116_);
lean_dec(v_x_2112_);
v___x_2127_ = lean_box(0);
return v___x_2127_;
}
}
}
else
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
lean_dec(v_x_2112_);
v___x_2128_ = lean_nat_add(v_m_2116_, v___x_2115_);
lean_dec(v_m_2116_);
v___x_2129_ = lean_nat_dec_le(v___x_2128_, v_x_2113_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
lean_dec(v___x_2128_);
lean_dec(v_x_2113_);
v___x_2130_ = lean_box(0);
return v___x_2130_;
}
else
{
v_x_2112_ = v___x_2128_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_2132_, lean_object* v_k_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2132_, v_k_2133_, v_x_2134_, v_x_2135_);
lean_dec_ref(v_k_2133_);
lean_dec_ref(v_as_2132_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2137_, lean_object* v_vals_2138_, lean_object* v_i_2139_, lean_object* v_k_2140_){
_start:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_array_get_size(v_keys_2137_);
v___x_2142_ = lean_nat_dec_lt(v_i_2139_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_i_2139_);
v___x_2143_ = lean_box(0);
return v___x_2143_;
}
else
{
lean_object* v_k_x27_2144_; uint8_t v___x_2145_; 
v_k_x27_2144_ = lean_array_fget_borrowed(v_keys_2137_, v_i_2139_);
v___x_2145_ = lean_name_eq(v_k_2140_, v_k_x27_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_i_2139_, v___x_2146_);
lean_dec(v_i_2139_);
v_i_2139_ = v___x_2147_;
goto _start;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_array_fget_borrowed(v_vals_2138_, v_i_2139_);
lean_dec(v_i_2139_);
lean_inc(v___x_2149_);
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2151_, lean_object* v_vals_2152_, lean_object* v_i_2153_, lean_object* v_k_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg(v_keys_2151_, v_vals_2152_, v_i_2153_, v_k_2154_);
lean_dec(v_k_2154_);
lean_dec_ref(v_vals_2152_);
lean_dec_ref(v_keys_2151_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg(lean_object* v_x_2156_, size_t v_x_2157_, lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
lean_object* v_es_2159_; lean_object* v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; lean_object* v_j_2163_; lean_object* v___x_2164_; 
v_es_2159_ = lean_ctor_get(v_x_2156_, 0);
v___x_2160_ = lean_box(2);
v___x_2161_ = ((size_t)31ULL);
v___x_2162_ = lean_usize_land(v_x_2157_, v___x_2161_);
v_j_2163_ = lean_usize_to_nat(v___x_2162_);
v___x_2164_ = lean_array_get_borrowed(v___x_2160_, v_es_2159_, v_j_2163_);
lean_dec(v_j_2163_);
switch(lean_obj_tag(v___x_2164_))
{
case 0:
{
lean_object* v_key_2165_; lean_object* v_val_2166_; uint8_t v___x_2167_; 
v_key_2165_ = lean_ctor_get(v___x_2164_, 0);
v_val_2166_ = lean_ctor_get(v___x_2164_, 1);
v___x_2167_ = lean_name_eq(v_x_2158_, v_key_2165_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_box(0);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; 
lean_inc(v_val_2166_);
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_val_2166_);
return v___x_2169_;
}
}
case 1:
{
lean_object* v_node_2170_; size_t v___x_2171_; size_t v___x_2172_; 
v_node_2170_ = lean_ctor_get(v___x_2164_, 0);
v___x_2171_ = ((size_t)5ULL);
v___x_2172_ = lean_usize_shift_right(v_x_2157_, v___x_2171_);
v_x_2156_ = v_node_2170_;
v_x_2157_ = v___x_2172_;
goto _start;
}
default: 
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_box(0);
return v___x_2174_;
}
}
}
else
{
lean_object* v_ks_2175_; lean_object* v_vs_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_ks_2175_ = lean_ctor_get(v_x_2156_, 0);
v_vs_2176_ = lean_ctor_get(v_x_2156_, 1);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg(v_ks_2175_, v_vs_2176_, v___x_2177_, v_x_2158_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
size_t v_x_1332__boxed_2182_; lean_object* v_res_2183_; 
v_x_1332__boxed_2182_ = lean_unbox_usize(v_x_2180_);
lean_dec(v_x_2180_);
v_res_2183_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg(v_x_2179_, v_x_1332__boxed_2182_, v_x_2181_);
lean_dec(v_x_2181_);
lean_dec_ref(v_x_2179_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
uint64_t v___y_2187_; 
if (lean_obj_tag(v_x_2185_) == 0)
{
uint64_t v___x_2190_; 
v___x_2190_ = 1723ULL;
v___y_2187_ = v___x_2190_;
goto v___jp_2186_;
}
else
{
uint64_t v_hash_2191_; 
v_hash_2191_ = lean_ctor_get_uint64(v_x_2185_, sizeof(void*)*2);
v___y_2187_ = v_hash_2191_;
goto v___jp_2186_;
}
v___jp_2186_:
{
size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_uint64_to_usize(v___y_2187_);
v___x_2189_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg(v_x_2184_, v___x_2188_, v_x_2185_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2192_, v_x_2193_);
lean_dec(v_x_2193_);
lean_dec_ref(v_x_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object* v_declName_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v_env_2199_; lean_object* v___x_2200_; lean_object* v___x_2210_; 
v___x_2198_ = lean_st_ref_get(v_a_2196_);
v_env_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_ref(v_env_2199_);
lean_dec(v___x_2198_);
v___x_2200_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2210_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2199_, v_declName_2195_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2211_; lean_object* v_toEnvExtension_2212_; lean_object* v_asyncMode_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_newEntries_2216_; lean_object* v___x_2217_; 
v___x_2211_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2212_ = lean_ctor_get(v___x_2211_, 0);
v_asyncMode_2213_ = lean_ctor_get(v_toEnvExtension_2212_, 2);
v___x_2214_ = lean_box(0);
lean_inc_ref(v_env_2199_);
v___x_2215_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2200_, v___x_2211_, v_env_2199_, v_asyncMode_2213_, v___x_2214_);
v_newEntries_2216_ = lean_ctor_get(v___x_2215_, 1);
lean_inc_ref(v_newEntries_2216_);
lean_dec(v___x_2215_);
v___x_2217_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_2216_, v_declName_2195_);
lean_dec_ref(v_newEntries_2216_);
if (lean_obj_tag(v___x_2217_) == 1)
{
lean_object* v___x_2218_; 
lean_dec_ref(v_env_2199_);
lean_dec(v_declName_2195_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
else
{
lean_dec(v___x_2217_);
goto v___jp_2201_;
}
}
else
{
lean_object* v_val_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2247_; 
v_val_2219_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2221_ = v___x_2210_;
v_isShared_2222_ = v_isSharedCheck_2247_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_val_2219_);
lean_dec(v___x_2210_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2247_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2223_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v___x_2224_ = 0;
v___x_2225_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2200_, v___x_2223_, v_env_2199_, v_val_2219_, v___x_2224_);
lean_dec(v_val_2219_);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_array_get_size(v___x_2225_);
v___x_2228_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v___x_2225_);
lean_del_object(v___x_2221_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_sub(v___x_2227_, v___x_2229_);
v___x_2231_ = lean_nat_dec_le(v___x_2226_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_dec(v___x_2230_);
lean_dec_ref(v___x_2225_);
lean_del_object(v___x_2221_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0));
lean_inc(v_declName_2195_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_declName_2195_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_2225_, v___x_2233_, v___x_2226_, v___x_2230_);
lean_dec_ref_known(v___x_2233_, 2);
lean_dec_ref(v___x_2225_);
if (lean_obj_tag(v___x_2234_) == 1)
{
lean_object* v_val_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_env_2199_);
lean_dec(v_declName_2195_);
v_val_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_val_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_keys_2239_; lean_object* v___x_2241_; 
v_keys_2239_ = lean_ctor_get(v_val_2235_, 1);
lean_inc_ref(v_keys_2239_);
lean_dec(v_val_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v_keys_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_keys_2239_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2241_);
v___x_2243_ = v___x_2221_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_dec(v___x_2234_);
lean_del_object(v___x_2221_);
goto v___jp_2201_;
}
}
}
}
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v_toEnvExtension_2203_; lean_object* v_asyncMode_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v_builtin_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2202_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2203_ = lean_ctor_get(v___x_2202_, 0);
v_asyncMode_2204_ = lean_ctor_get(v_toEnvExtension_2203_, 2);
v___x_2205_ = lean_box(0);
v___x_2206_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2200_, v___x_2202_, v_env_2199_, v_asyncMode_2204_, v___x_2205_);
v_builtin_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc_ref(v_builtin_2207_);
lean_dec(v___x_2206_);
v___x_2208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_2207_, v_declName_2195_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_builtin_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2248_, v_a_2249_);
lean_dec(v_a_2249_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object* v_declName_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2252_, v_a_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object* v_declName_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_2262_, lean_object* v_m_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2263_, v_a_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_2266_, lean_object* v_m_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_2266_, v_m_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_m_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2271_, v_x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_2274_, v_x_2275_, v_x_2276_);
lean_dec(v_x_2276_);
lean_dec_ref(v_x_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object* v_as_2278_, lean_object* v_k_2279_, lean_object* v_x_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2278_, v_k_2279_, v_x_2280_, v_x_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_2284_, lean_object* v_k_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(v_as_2284_, v_k_2285_, v_x_2286_, v_x_2287_, v_x_2288_);
lean_dec_ref(v_k_2285_);
lean_dec_ref(v_as_2284_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1(lean_object* v_00_u03b2_2290_, lean_object* v_x_2291_, size_t v_x_2292_, lean_object* v_x_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___redArg(v_x_2291_, v_x_2292_, v_x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
size_t v_x_1511__boxed_2299_; lean_object* v_res_2300_; 
v_x_1511__boxed_2299_ = lean_unbox_usize(v_x_2297_);
lean_dec(v_x_2297_);
v_res_2300_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1(v_00_u03b2_2295_, v_x_2296_, v_x_1511__boxed_2299_, v_x_2298_);
lean_dec(v_x_2298_);
lean_dec_ref(v_x_2296_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2301_, lean_object* v_keys_2302_, lean_object* v_vals_2303_, lean_object* v_heq_2304_, lean_object* v_i_2305_, lean_object* v_k_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___redArg(v_keys_2302_, v_vals_2303_, v_i_2305_, v_k_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2308_, lean_object* v_keys_2309_, lean_object* v_vals_2310_, lean_object* v_heq_2311_, lean_object* v_i_2312_, lean_object* v_k_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__1_spec__2(v_00_u03b2_2308_, v_keys_2309_, v_vals_2310_, v_heq_2311_, v_i_2312_, v_k_2313_);
lean_dec(v_k_2313_);
lean_dec_ref(v_vals_2310_);
lean_dec_ref(v_keys_2309_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object* v_declName_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___x_2318_; lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2333_; 
v___x_2318_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2315_, v_a_2316_);
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2333_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2333_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
if (lean_obj_tag(v_a_2319_) == 0)
{
uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2323_ = 0;
v___x_2324_ = lean_box(v___x_2323_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
else
{
uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_dec_ref_known(v_a_2319_, 1);
v___x_2328_ = 1;
v___x_2329_ = lean_box(v___x_2328_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2329_);
v___x_2331_ = v___x_2321_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object* v_declName_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2334_, v_a_2335_);
lean_dec(v_a_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object* v_declName_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2338_, v_a_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object* v_declName_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object* v_declName_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v_env_2352_; lean_object* v___x_2353_; lean_object* v_toEnvExtension_2354_; lean_object* v_asyncMode_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_builtin_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2351_ = lean_st_ref_get(v_a_2349_);
v_env_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc_ref(v_env_2352_);
lean_dec(v___x_2351_);
v___x_2353_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2354_ = lean_ctor_get(v___x_2353_, 0);
v_asyncMode_2355_ = lean_ctor_get(v_toEnvExtension_2354_, 2);
v___x_2356_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2357_ = lean_box(0);
v___x_2358_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2356_, v___x_2353_, v_env_2352_, v_asyncMode_2355_, v___x_2357_);
v_builtin_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc_ref(v_builtin_2359_);
lean_dec(v___x_2358_);
v___x_2360_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_2359_, v_declName_2348_);
lean_dec_ref(v_builtin_2359_);
v___x_2361_ = lean_box(v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object* v_declName_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec(v_declName_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object* v_declName_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2367_, v_a_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object* v_declName_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_declName_2372_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object* v_declName_2377_, lean_object* v_keys_2378_, lean_object* v_s_2379_){
_start:
{
lean_object* v_builtin_2380_; lean_object* v_newEntries_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
v_builtin_2380_ = lean_ctor_get(v_s_2379_, 0);
v_newEntries_2381_ = lean_ctor_get(v_s_2379_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_s_2379_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2383_ = v_s_2379_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_newEntries_2381_);
lean_inc(v_builtin_2380_);
lean_dec(v_s_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_2381_, v_declName_2377_, v_keys_2378_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v___x_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_builtin_2380_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
lean_ctor_set(v___x_2395_, 2, v___x_2394_);
lean_ctor_set(v___x_2395_, 3, v___x_2394_);
lean_ctor_set(v___x_2395_, 4, v___x_2393_);
lean_ctor_set(v___x_2395_, 5, v___x_2393_);
lean_ctor_set(v___x_2395_, 6, v___x_2393_);
lean_ctor_set(v___x_2395_, 7, v___x_2393_);
lean_ctor_set(v___x_2395_, 8, v___x_2393_);
lean_ctor_set(v___x_2395_, 9, v___x_2393_);
lean_ctor_set(v___x_2395_, 10, v___x_2393_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = lean_unsigned_to_nat(32u);
v___x_2397_ = lean_mk_empty_array_with_capacity(v___x_2396_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2399_ = ((size_t)5ULL);
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_unsigned_to_nat(32u);
v___x_2402_ = lean_mk_empty_array_with_capacity(v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
v___x_2404_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2402_);
lean_ctor_set(v___x_2404_, 2, v___x_2400_);
lean_ctor_set(v___x_2404_, 3, v___x_2400_);
lean_ctor_set_usize(v___x_2404_, 4, v___x_2399_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2405_ = lean_box(1);
v___x_2406_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
v___x_2407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v___x_2406_);
lean_ctor_set(v___x_2408_, 2, v___x_2405_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object* v_msgData_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_env_2414_; lean_object* v_options_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2413_ = lean_st_ref_get(v___y_2411_);
v_env_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_env_2414_);
lean_dec(v___x_2413_);
v_options_2415_ = lean_ctor_get(v___y_2410_, 2);
v___x_2416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2415_);
v___x_2418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2418_, 0, v_env_2414_);
lean_ctor_set(v___x_2418_, 1, v___x_2416_);
lean_ctor_set(v___x_2418_, 2, v___x_2417_);
lean_ctor_set(v___x_2418_, 3, v_options_2415_);
v___x_2419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_msgData_2409_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_ref_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_ref_2430_ = lean_ctor_get(v___y_2427_, 5);
v___x_2431_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_2426_, v___y_2427_, v___y_2428_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_inc(v_ref_2430_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_ref_2430_);
lean_ctor_set(v___x_2436_, 1, v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object* v_msg_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
return v_res_2445_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0(void){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2446_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3));
v___x_2453_ = l_Lean_stringToMessageData(v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object* v_declName_2459_, lean_object* v_keys_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v_env_2465_; lean_object* v___f_2466_; lean_object* v___y_2468_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2516_; 
v___x_2464_ = lean_st_ref_get(v_a_2462_);
v_env_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc_ref(v_env_2465_);
lean_dec(v___x_2464_);
lean_inc(v_declName_2459_);
v___f_2466_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0), 3, 2);
lean_closure_set(v___f_2466_, 0, v_declName_2459_);
lean_closure_set(v___f_2466_, 1, v_keys_2460_);
v___x_2516_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2465_, v_declName_2459_);
lean_dec_ref(v_env_2465_);
if (lean_obj_tag(v___x_2516_) == 0)
{
v___y_2496_ = v_a_2461_;
v___y_2497_ = v_a_2462_;
goto v___jp_2495_;
}
else
{
uint8_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref_known(v___x_2516_, 1);
lean_dec_ref(v___f_2466_);
v___x_2517_ = 0;
v___x_2518_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2519_ = l_Lean_MessageData_ofConstName(v_declName_2459_, v___x_2517_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2522_, v_a_2461_, v_a_2462_);
return v___x_2523_;
}
v___jp_2467_:
{
lean_object* v___x_2469_; lean_object* v_env_2470_; lean_object* v_nextMacroScope_2471_; lean_object* v_ngen_2472_; lean_object* v_auxDeclNGen_2473_; lean_object* v_traceState_2474_; lean_object* v_messages_2475_; lean_object* v_infoState_2476_; lean_object* v_snapshotTasks_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2493_; 
v___x_2469_ = lean_st_ref_take(v___y_2468_);
v_env_2470_ = lean_ctor_get(v___x_2469_, 0);
v_nextMacroScope_2471_ = lean_ctor_get(v___x_2469_, 1);
v_ngen_2472_ = lean_ctor_get(v___x_2469_, 2);
v_auxDeclNGen_2473_ = lean_ctor_get(v___x_2469_, 3);
v_traceState_2474_ = lean_ctor_get(v___x_2469_, 4);
v_messages_2475_ = lean_ctor_get(v___x_2469_, 6);
v_infoState_2476_ = lean_ctor_get(v___x_2469_, 7);
v_snapshotTasks_2477_ = lean_ctor_get(v___x_2469_, 8);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v___x_2469_, 5);
lean_dec(v_unused_2494_);
v___x_2479_ = v___x_2469_;
v_isShared_2480_ = v_isSharedCheck_2493_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_snapshotTasks_2477_);
lean_inc(v_infoState_2476_);
lean_inc(v_messages_2475_);
lean_inc(v_traceState_2474_);
lean_inc(v_auxDeclNGen_2473_);
lean_inc(v_ngen_2472_);
lean_inc(v_nextMacroScope_2471_);
lean_inc(v_env_2470_);
lean_dec(v___x_2469_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2493_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v_toEnvExtension_2482_; lean_object* v_asyncMode_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2481_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2482_ = lean_ctor_get(v___x_2481_, 0);
v_asyncMode_2483_ = lean_ctor_get(v_toEnvExtension_2482_, 2);
v___x_2484_ = lean_box(0);
v___x_2485_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2481_, v_env_2470_, v___f_2466_, v_asyncMode_2483_, v___x_2484_);
v___x_2486_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 5, v___x_2486_);
lean_ctor_set(v___x_2479_, 0, v___x_2485_);
v___x_2488_ = v___x_2479_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_nextMacroScope_2471_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_ngen_2472_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_auxDeclNGen_2473_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_traceState_2474_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_messages_2475_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_infoState_2476_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_snapshotTasks_2477_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_st_ref_put(v___y_2468_, v___x_2488_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
}
v___jp_2495_:
{
lean_object* v___x_2498_; 
lean_inc(v_declName_2459_);
v___x_2498_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2459_, v___y_2497_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; uint8_t v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = lean_unbox(v_a_2499_);
lean_dec(v_a_2499_);
if (v___x_2500_ == 0)
{
lean_dec(v_declName_2459_);
v___y_2468_ = v___y_2497_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v___f_2466_);
v___x_2501_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2502_ = 0;
v___x_2503_ = l_Lean_MessageData_ofConstName(v_declName_2459_, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2501_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2506_, v___y_2496_, v___y_2497_);
return v___x_2507_;
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v___f_2466_);
lean_dec(v_declName_2459_);
v_a_2508_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2498_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2498_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object* v_declName_2524_, lean_object* v_keys_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2524_, v_keys_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object* v_00_u03b1_2530_, lean_object* v_msg_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2531_, v___y_2532_, v___y_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object* v_00_u03b1_2536_, lean_object* v_msg_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(v_00_u03b1_2536_, v_msg_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_2542_){
_start:
{
if (lean_obj_tag(v_e_2542_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2552_; 
v_a_2544_ = lean_ctor_get(v_e_2542_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_e_2542_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2546_ = v_e_2542_;
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v_e_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = lean_mk_io_user_error(v_a_2544_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 1);
lean_ctor_set(v___x_2546_, 0, v___x_2548_);
v___x_2550_ = v___x_2546_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_a_2553_ = lean_ctor_get(v_e_2542_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_e_2542_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v_e_2542_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v_e_2542_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 0);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_2564_, lean_object* v_e_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2565_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_e_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(v_00_u03b1_2568_, v_e_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object* v_declName_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_env_2582_; lean_object* v_opts_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
v_env_2582_ = lean_ctor_get(v_a_2580_, 0);
v_opts_2583_ = lean_ctor_get(v_a_2580_, 1);
v___x_2584_ = 0;
lean_inc(v_declName_2579_);
lean_inc_ref(v_env_2582_);
v___x_2585_ = l_Lean_Environment_find_x3f(v_env_2582_, v_declName_2579_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2586_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0));
v___x_2587_ = 1;
v___x_2588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2579_, v___x_2587_);
v___x_2589_ = lean_string_append(v___x_2586_, v___x_2588_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2591_ = lean_string_append(v___x_2589_, v___x_2590_);
v___x_2592_ = lean_mk_io_user_error(v___x_2591_);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2639_; 
v_val_2594_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2596_ = v___x_2585_;
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_val_2594_);
lean_dec(v___x_2585_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_ConstantInfo_type(v_val_2594_);
if (lean_obj_tag(v___x_2615_) == 4)
{
lean_object* v_declName_2616_; 
v_declName_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_declName_2616_);
lean_dec_ref_known(v___x_2615_, 2);
if (lean_obj_tag(v_declName_2616_) == 1)
{
lean_object* v_pre_2617_; 
v_pre_2617_ = lean_ctor_get(v_declName_2616_, 0);
lean_inc(v_pre_2617_);
if (lean_obj_tag(v_pre_2617_) == 1)
{
lean_object* v_pre_2618_; 
v_pre_2618_ = lean_ctor_get(v_pre_2617_, 0);
lean_inc(v_pre_2618_);
if (lean_obj_tag(v_pre_2618_) == 1)
{
lean_object* v_pre_2619_; 
v_pre_2619_ = lean_ctor_get(v_pre_2618_, 0);
lean_inc(v_pre_2619_);
if (lean_obj_tag(v_pre_2619_) == 1)
{
lean_object* v_pre_2620_; 
v_pre_2620_ = lean_ctor_get(v_pre_2619_, 0);
lean_inc(v_pre_2620_);
if (lean_obj_tag(v_pre_2620_) == 1)
{
lean_object* v_pre_2621_; 
v_pre_2621_ = lean_ctor_get(v_pre_2620_, 0);
if (lean_obj_tag(v_pre_2621_) == 0)
{
lean_object* v_str_2622_; lean_object* v_str_2623_; lean_object* v_str_2624_; lean_object* v_str_2625_; lean_object* v_str_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v_str_2622_ = lean_ctor_get(v_declName_2616_, 1);
lean_inc_ref(v_str_2622_);
lean_dec_ref_known(v_declName_2616_, 2);
v_str_2623_ = lean_ctor_get(v_pre_2617_, 1);
lean_inc_ref(v_str_2623_);
lean_dec_ref_known(v_pre_2617_, 2);
v_str_2624_ = lean_ctor_get(v_pre_2618_, 1);
lean_inc_ref(v_str_2624_);
lean_dec_ref_known(v_pre_2618_, 2);
v_str_2625_ = lean_ctor_get(v_pre_2619_, 1);
lean_inc_ref(v_str_2625_);
lean_dec_ref_known(v_pre_2619_, 2);
v_str_2626_ = lean_ctor_get(v_pre_2620_, 1);
lean_inc_ref(v_str_2626_);
lean_dec_ref_known(v_pre_2620_, 2);
v___x_2627_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0));
v___x_2628_ = lean_string_dec_eq(v_str_2626_, v___x_2627_);
lean_dec_ref(v_str_2626_);
if (v___x_2628_ == 0)
{
lean_dec_ref(v_str_2625_);
lean_dec_ref(v_str_2624_);
lean_dec_ref(v_str_2623_);
lean_dec_ref(v_str_2622_);
goto v___jp_2598_;
}
else
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1));
v___x_2630_ = lean_string_dec_eq(v_str_2625_, v___x_2629_);
lean_dec_ref(v_str_2625_);
if (v___x_2630_ == 0)
{
lean_dec_ref(v_str_2624_);
lean_dec_ref(v_str_2623_);
lean_dec_ref(v_str_2622_);
goto v___jp_2598_;
}
else
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4));
v___x_2632_ = lean_string_dec_eq(v_str_2624_, v___x_2631_);
lean_dec_ref(v_str_2624_);
if (v___x_2632_ == 0)
{
lean_dec_ref(v_str_2623_);
lean_dec_ref(v_str_2622_);
goto v___jp_2598_;
}
else
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5));
v___x_2634_ = lean_string_dec_eq(v_str_2623_, v___x_2633_);
lean_dec_ref(v_str_2623_);
if (v___x_2634_ == 0)
{
lean_dec_ref(v_str_2622_);
goto v___jp_2598_;
}
else
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6));
v___x_2636_ = lean_string_dec_eq(v_str_2622_, v___x_2635_);
lean_dec_ref(v_str_2622_);
if (v___x_2636_ == 0)
{
goto v___jp_2598_;
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_del_object(v___x_2596_);
lean_dec(v_val_2594_);
v___x_2637_ = l_Lean_Environment_evalConst___redArg(v_env_2582_, v_opts_2583_, v_declName_2579_, v___x_2636_);
lean_dec(v_declName_2579_);
v___x_2638_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_2637_);
return v___x_2638_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2620_, 2);
lean_dec_ref_known(v_pre_2619_, 2);
lean_dec_ref_known(v_pre_2618_, 2);
lean_dec_ref_known(v_pre_2617_, 2);
lean_dec_ref_known(v_declName_2616_, 2);
goto v___jp_2598_;
}
}
else
{
lean_dec_ref_known(v_pre_2619_, 2);
lean_dec(v_pre_2620_);
lean_dec_ref_known(v_pre_2618_, 2);
lean_dec_ref_known(v_pre_2617_, 2);
lean_dec_ref_known(v_declName_2616_, 2);
goto v___jp_2598_;
}
}
else
{
lean_dec(v_pre_2619_);
lean_dec_ref_known(v_pre_2618_, 2);
lean_dec_ref_known(v_pre_2617_, 2);
lean_dec_ref_known(v_declName_2616_, 2);
goto v___jp_2598_;
}
}
else
{
lean_dec_ref_known(v_pre_2617_, 2);
lean_dec(v_pre_2618_);
lean_dec_ref_known(v_declName_2616_, 2);
goto v___jp_2598_;
}
}
else
{
lean_dec(v_pre_2617_);
lean_dec_ref_known(v_declName_2616_, 2);
goto v___jp_2598_;
}
}
else
{
lean_dec(v_declName_2616_);
goto v___jp_2598_;
}
}
else
{
lean_dec_ref(v___x_2615_);
goto v___jp_2598_;
}
v___jp_2598_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2599_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2));
v___x_2600_ = l_Lean_privateToUserName(v_declName_2579_);
v___x_2601_ = 1;
v___x_2602_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2600_, v___x_2601_);
v___x_2603_ = lean_string_append(v___x_2599_, v___x_2602_);
lean_dec_ref(v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3));
v___x_2605_ = lean_string_append(v___x_2603_, v___x_2604_);
v___x_2606_ = l_Lean_ConstantInfo_type(v_val_2594_);
lean_dec(v_val_2594_);
v___x_2607_ = lean_expr_dbg_to_string(v___x_2606_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = lean_string_append(v___x_2605_, v___x_2607_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2610_ = lean_string_append(v___x_2608_, v___x_2609_);
v___x_2611_ = lean_mk_io_user_error(v___x_2610_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2611_);
v___x_2613_ = v___x_2596_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object* v_declName_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2640_, v_a_2641_);
lean_dec_ref(v_a_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object* v_e_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_declName_2647_; lean_object* v___x_2648_; 
v_declName_2647_ = lean_ctor_get(v_e_2644_, 0);
lean_inc(v_declName_2647_);
v___x_2648_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2647_, v_a_2645_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2657_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2657_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_e_2644_);
lean_ctor_set(v___x_2653_, 1, v_a_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2653_);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref(v_e_2644_);
v_a_2658_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2648_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2648_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object* v_e_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2666_, v_a_2667_);
lean_dec_ref(v_a_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
v___x_2672_ = lean_st_mk_ref(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___y_2676_){
_start:
{
lean_inc_ref(v___y_2676_);
return v___y_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_2677_);
lean_dec_ref(v___y_2677_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_2680_, v___y_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2684_, v___y_2685_, v___y_2686_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_x_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_e_2689_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2690_; 
v_toCbvSimprocOLeanEntry_2690_ = lean_ctor_get(v_e_2689_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2690_);
return v_toCbvSimprocOLeanEntry_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_e_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_2691_);
lean_dec_ref(v_e_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_s_2693_, lean_object* v_e_2694_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2695_; lean_object* v_proc_2696_; lean_object* v_declName_2697_; uint8_t v_phase_2698_; lean_object* v_keys_2699_; lean_object* v___x_2700_; 
v_toCbvSimprocOLeanEntry_2695_ = lean_ctor_get(v_e_2694_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2695_);
v_proc_2696_ = lean_ctor_get(v_e_2694_, 1);
lean_inc_ref(v_proc_2696_);
lean_dec_ref(v_e_2694_);
v_declName_2697_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2695_, 0);
lean_inc(v_declName_2697_);
v_phase_2698_ = lean_ctor_get_uint8(v_toCbvSimprocOLeanEntry_2695_, sizeof(void*)*2);
v_keys_2699_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2695_, 1);
lean_inc_ref(v_keys_2699_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_2695_);
v___x_2700_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_2693_, v_keys_2699_, v_declName_2697_, v_phase_2698_, v_proc_2696_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_a_2702_);
lean_inc_ref_n(v___x_2703_, 2);
v___x_2704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2705_, v_a_2706_);
lean_dec_ref(v_x_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___x_2708_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_st_ref_get(v___x_2708_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___x_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2712_);
lean_dec(v___x_2712_);
return v_res_2714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___f_2724_; 
v___x_2723_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___f_2724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2724_, 0, v___x_2723_);
return v___f_2724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2725_; lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___f_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___f_2725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___x_2732_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v___f_2730_);
lean_ctor_set(v___x_2732_, 2, v___f_2729_);
lean_ctor_set(v___x_2732_, 3, v___f_2728_);
lean_ctor_set(v___x_2732_, 4, v___f_2727_);
lean_ctor_set(v___x_2732_, 5, v___f_2726_);
lean_ctor_set(v___x_2732_, 6, v___f_2725_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2735_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object* v_declName_2738_, lean_object* v_s_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_2739_, v_declName_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2741_, lean_object* v_i_2742_, lean_object* v_k_2743_){
_start:
{
lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2744_ = lean_array_get_size(v_keys_2741_);
v___x_2745_ = lean_nat_dec_lt(v_i_2742_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_dec(v_i_2742_);
return v___x_2745_;
}
else
{
lean_object* v_k_x27_2746_; uint8_t v___x_2747_; 
v_k_x27_2746_ = lean_array_fget_borrowed(v_keys_2741_, v_i_2742_);
v___x_2747_ = lean_name_eq(v_k_2743_, v_k_x27_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_unsigned_to_nat(1u);
v___x_2749_ = lean_nat_add(v_i_2742_, v___x_2748_);
lean_dec(v_i_2742_);
v_i_2742_ = v___x_2749_;
goto _start;
}
else
{
lean_dec(v_i_2742_);
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2751_, lean_object* v_i_2752_, lean_object* v_k_2753_){
_start:
{
uint8_t v_res_2754_; lean_object* v_r_2755_; 
v_res_2754_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2751_, v_i_2752_, v_k_2753_);
lean_dec(v_k_2753_);
lean_dec_ref(v_keys_2751_);
v_r_2755_ = lean_box(v_res_2754_);
return v_r_2755_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_2756_, size_t v_x_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2756_) == 0)
{
lean_object* v_es_2759_; lean_object* v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; lean_object* v_j_2763_; lean_object* v___x_2764_; 
v_es_2759_ = lean_ctor_get(v_x_2756_, 0);
v___x_2760_ = lean_box(2);
v___x_2761_ = ((size_t)31ULL);
v___x_2762_ = lean_usize_land(v_x_2757_, v___x_2761_);
v_j_2763_ = lean_usize_to_nat(v___x_2762_);
v___x_2764_ = lean_array_get_borrowed(v___x_2760_, v_es_2759_, v_j_2763_);
lean_dec(v_j_2763_);
switch(lean_obj_tag(v___x_2764_))
{
case 0:
{
lean_object* v_key_2765_; uint8_t v___x_2766_; 
v_key_2765_ = lean_ctor_get(v___x_2764_, 0);
v___x_2766_ = lean_name_eq(v_x_2758_, v_key_2765_);
return v___x_2766_;
}
case 1:
{
lean_object* v_node_2767_; size_t v___x_2768_; size_t v___x_2769_; 
v_node_2767_ = lean_ctor_get(v___x_2764_, 0);
v___x_2768_ = ((size_t)5ULL);
v___x_2769_ = lean_usize_shift_right(v_x_2757_, v___x_2768_);
v_x_2756_ = v_node_2767_;
v_x_2757_ = v___x_2769_;
goto _start;
}
default: 
{
uint8_t v___x_2771_; 
v___x_2771_ = 0;
return v___x_2771_;
}
}
}
else
{
lean_object* v_ks_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_ks_2772_ = lean_ctor_get(v_x_2756_, 0);
v___x_2773_ = lean_unsigned_to_nat(0u);
v___x_2774_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_2772_, v___x_2773_, v_x_2758_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_){
_start:
{
size_t v_x_546__boxed_2778_; uint8_t v_res_2779_; lean_object* v_r_2780_; 
v_x_546__boxed_2778_ = lean_unbox_usize(v_x_2776_);
lean_dec(v_x_2776_);
v_res_2779_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2775_, v_x_546__boxed_2778_, v_x_2777_);
lean_dec(v_x_2777_);
lean_dec_ref(v_x_2775_);
v_r_2780_ = lean_box(v_res_2779_);
return v_r_2780_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
uint64_t v___y_2784_; 
if (lean_obj_tag(v_x_2782_) == 0)
{
uint64_t v___x_2787_; 
v___x_2787_ = 1723ULL;
v___y_2784_ = v___x_2787_;
goto v___jp_2783_;
}
else
{
uint64_t v_hash_2788_; 
v_hash_2788_ = lean_ctor_get_uint64(v_x_2782_, sizeof(void*)*2);
v___y_2784_ = v_hash_2788_;
goto v___jp_2783_;
}
v___jp_2783_:
{
size_t v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = lean_uint64_to_usize(v___y_2784_);
v___x_2786_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2781_, v___x_2785_, v_x_2782_);
return v___x_2786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_2789_, lean_object* v_x_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2789_, v_x_2790_);
lean_dec(v_x_2790_);
lean_dec_ref(v_x_2789_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1));
v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object* v_declName_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v_env_2803_; lean_object* v___x_2804_; lean_object* v_ext_2805_; lean_object* v_toEnvExtension_2806_; lean_object* v_asyncMode_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_simprocNames_2810_; lean_object* v___f_2811_; lean_object* v___y_2813_; uint8_t v___x_2836_; 
v___x_2802_ = lean_st_ref_get(v_a_2800_);
v_env_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2803_);
lean_dec(v___x_2802_);
v___x_2804_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_2805_ = lean_ctor_get(v___x_2804_, 1);
v_toEnvExtension_2806_ = lean_ctor_get(v_ext_2805_, 0);
v_asyncMode_2807_ = lean_ctor_get(v_toEnvExtension_2806_, 2);
v___x_2808_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_2809_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2808_, v___x_2804_, v_env_2803_, v_asyncMode_2807_);
v_simprocNames_2810_ = lean_ctor_get(v___x_2809_, 3);
lean_inc_ref(v_simprocNames_2810_);
lean_dec(v___x_2809_);
lean_inc(v_declName_2798_);
v___f_2811_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_2811_, 0, v_declName_2798_);
v___x_2836_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_2810_, v_declName_2798_);
lean_dec_ref(v_simprocNames_2810_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec_ref(v___f_2811_);
v___x_2837_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0);
v___x_2838_ = l_Lean_MessageData_ofConstName(v_declName_2798_, v___x_2836_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2841_, v_a_2799_, v_a_2800_);
return v___x_2842_;
}
else
{
lean_dec(v_declName_2798_);
v___y_2813_ = v_a_2800_;
goto v___jp_2812_;
}
v___jp_2812_:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; lean_object* v_nextMacroScope_2816_; lean_object* v_ngen_2817_; lean_object* v_auxDeclNGen_2818_; lean_object* v_traceState_2819_; lean_object* v_messages_2820_; lean_object* v_infoState_2821_; lean_object* v_snapshotTasks_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2834_; 
v___x_2814_ = lean_st_ref_take(v___y_2813_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
v_nextMacroScope_2816_ = lean_ctor_get(v___x_2814_, 1);
v_ngen_2817_ = lean_ctor_get(v___x_2814_, 2);
v_auxDeclNGen_2818_ = lean_ctor_get(v___x_2814_, 3);
v_traceState_2819_ = lean_ctor_get(v___x_2814_, 4);
v_messages_2820_ = lean_ctor_get(v___x_2814_, 6);
v_infoState_2821_ = lean_ctor_get(v___x_2814_, 7);
v_snapshotTasks_2822_ = lean_ctor_get(v___x_2814_, 8);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; 
v_unused_2835_ = lean_ctor_get(v___x_2814_, 5);
lean_dec(v_unused_2835_);
v___x_2824_ = v___x_2814_;
v_isShared_2825_ = v_isSharedCheck_2834_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_snapshotTasks_2822_);
lean_inc(v_infoState_2821_);
lean_inc(v_messages_2820_);
lean_inc(v_traceState_2819_);
lean_inc(v_auxDeclNGen_2818_);
lean_inc(v_ngen_2817_);
lean_inc(v_nextMacroScope_2816_);
lean_inc(v_env_2815_);
lean_dec(v___x_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2834_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2804_, v_env_2815_, v___f_2811_);
v___x_2827_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 5, v___x_2827_);
lean_ctor_set(v___x_2824_, 0, v___x_2826_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_nextMacroScope_2816_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_ngen_2817_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_auxDeclNGen_2818_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_traceState_2819_);
lean_ctor_set(v_reuseFailAlloc_2833_, 5, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2833_, 6, v_messages_2820_);
lean_ctor_set(v_reuseFailAlloc_2833_, 7, v_infoState_2821_);
lean_ctor_set(v_reuseFailAlloc_2833_, 8, v_snapshotTasks_2822_);
v___x_2829_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = lean_st_ref_put(v___y_2813_, v___x_2829_);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object* v_declName_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2843_, v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object* v_00_u03b2_2848_, lean_object* v_x_2849_, lean_object* v_x_2850_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2849_, v_x_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_2852_, lean_object* v_x_2853_, lean_object* v_x_2854_){
_start:
{
uint8_t v_res_2855_; lean_object* v_r_2856_; 
v_res_2855_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(v_00_u03b2_2852_, v_x_2853_, v_x_2854_);
lean_dec(v_x_2854_);
lean_dec_ref(v_x_2853_);
v_r_2856_ = lean_box(v_res_2855_);
return v_r_2856_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_2857_, lean_object* v_x_2858_, size_t v_x_2859_, lean_object* v_x_2860_){
_start:
{
uint8_t v___x_2861_; 
v___x_2861_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2858_, v_x_2859_, v_x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2862_, lean_object* v_x_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
size_t v_x_694__boxed_2866_; uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_x_694__boxed_2866_ = lean_unbox_usize(v_x_2864_);
lean_dec(v_x_2864_);
v_res_2867_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_2862_, v_x_2863_, v_x_694__boxed_2866_, v_x_2865_);
lean_dec(v_x_2865_);
lean_dec_ref(v_x_2863_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2869_, lean_object* v_keys_2870_, lean_object* v_vals_2871_, lean_object* v_heq_2872_, lean_object* v_i_2873_, lean_object* v_k_2874_){
_start:
{
uint8_t v___x_2875_; 
v___x_2875_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2870_, v_i_2873_, v_k_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2876_, lean_object* v_keys_2877_, lean_object* v_vals_2878_, lean_object* v_heq_2879_, lean_object* v_i_2880_, lean_object* v_k_2881_){
_start:
{
uint8_t v_res_2882_; lean_object* v_r_2883_; 
v_res_2882_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_2876_, v_keys_2877_, v_vals_2878_, v_heq_2879_, v_i_2880_, v_k_2881_);
lean_dec(v_k_2881_);
lean_dec_ref(v_vals_2878_);
lean_dec_ref(v_keys_2877_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object* v_ext_2884_, lean_object* v_b_2885_, uint8_t v_kind_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_currNamespace_2890_; lean_object* v___x_2891_; lean_object* v_env_2892_; lean_object* v_nextMacroScope_2893_; lean_object* v_ngen_2894_; lean_object* v_auxDeclNGen_2895_; lean_object* v_traceState_2896_; lean_object* v_messages_2897_; lean_object* v_infoState_2898_; lean_object* v_snapshotTasks_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2911_; 
v_currNamespace_2890_ = lean_ctor_get(v___y_2887_, 6);
v___x_2891_ = lean_st_ref_take(v___y_2888_);
v_env_2892_ = lean_ctor_get(v___x_2891_, 0);
v_nextMacroScope_2893_ = lean_ctor_get(v___x_2891_, 1);
v_ngen_2894_ = lean_ctor_get(v___x_2891_, 2);
v_auxDeclNGen_2895_ = lean_ctor_get(v___x_2891_, 3);
v_traceState_2896_ = lean_ctor_get(v___x_2891_, 4);
v_messages_2897_ = lean_ctor_get(v___x_2891_, 6);
v_infoState_2898_ = lean_ctor_get(v___x_2891_, 7);
v_snapshotTasks_2899_ = lean_ctor_get(v___x_2891_, 8);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; 
v_unused_2912_ = lean_ctor_get(v___x_2891_, 5);
lean_dec(v_unused_2912_);
v___x_2901_ = v___x_2891_;
v_isShared_2902_ = v_isSharedCheck_2911_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_snapshotTasks_2899_);
lean_inc(v_infoState_2898_);
lean_inc(v_messages_2897_);
lean_inc(v_traceState_2896_);
lean_inc(v_auxDeclNGen_2895_);
lean_inc(v_ngen_2894_);
lean_inc(v_nextMacroScope_2893_);
lean_inc(v_env_2892_);
lean_dec(v___x_2891_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2911_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
lean_inc(v_currNamespace_2890_);
v___x_2903_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2892_, v_ext_2884_, v_b_2885_, v_kind_2886_, v_currNamespace_2890_);
v___x_2904_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 5, v___x_2904_);
lean_ctor_set(v___x_2901_, 0, v___x_2903_);
v___x_2906_ = v___x_2901_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_nextMacroScope_2893_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_ngen_2894_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_auxDeclNGen_2895_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_traceState_2896_);
lean_ctor_set(v_reuseFailAlloc_2910_, 5, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2910_, 6, v_messages_2897_);
lean_ctor_set(v_reuseFailAlloc_2910_, 7, v_infoState_2898_);
lean_ctor_set(v_reuseFailAlloc_2910_, 8, v_snapshotTasks_2899_);
v___x_2906_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_st_ref_put(v___y_2888_, v___x_2906_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_2913_, lean_object* v_b_2914_, lean_object* v_kind_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v_kind_boxed_2919_; lean_object* v_res_2920_; 
v_kind_boxed_2919_ = lean_unbox(v_kind_2915_);
v_res_2920_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2913_, v_b_2914_, v_kind_boxed_2919_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object* v_00_u03b1_2921_, lean_object* v_00_u03b2_2922_, lean_object* v_00_u03c3_2923_, lean_object* v_ext_2924_, lean_object* v_b_2925_, uint8_t v_kind_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2924_, v_b_2925_, v_kind_2926_, v___y_2927_, v___y_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_00_u03c3_2933_, lean_object* v_ext_2934_, lean_object* v_b_2935_, lean_object* v_kind_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v_kind_boxed_2940_; lean_object* v_res_2941_; 
v_kind_boxed_2940_ = lean_unbox(v_kind_2936_);
v_res_2941_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(v_00_u03b1_2931_, v_00_u03b2_2932_, v_00_u03c3_2933_, v_ext_2934_, v_b_2935_, v_kind_boxed_2940_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
return v_res_2941_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0));
v___x_2944_ = l_Lean_stringToMessageData(v___x_2943_);
return v___x_2944_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object* v_declName_2948_, uint8_t v_kind_2949_, uint8_t v_phase_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2954_; lean_object* v_env_2955_; lean_object* v_options_2956_; lean_object* v_ref_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2954_ = lean_st_ref_get(v_a_2952_);
v_env_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_ref(v_env_2955_);
lean_dec(v___x_2954_);
v_options_2956_ = lean_ctor_get(v_a_2951_, 2);
v_ref_2957_ = lean_ctor_get(v_a_2951_, 5);
lean_inc_ref(v_options_2956_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v_env_2955_);
lean_ctor_set(v___x_2958_, 1, v_options_2956_);
lean_inc(v_declName_2948_);
v___x_2959_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2948_, v___x_2958_);
lean_dec_ref_known(v___x_2958_, 2);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v_a_2962_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
lean_inc(v_declName_2948_);
v___x_2961_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2948_, v_a_2952_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
if (lean_obj_tag(v_a_2962_) == 1)
{
lean_object* v_val_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_val_2963_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_val_2963_);
lean_dec_ref_known(v_a_2962_, 1);
v___x_2964_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v___x_2965_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2965_, 0, v_declName_2948_);
lean_ctor_set(v___x_2965_, 1, v_val_2963_);
lean_ctor_set_uint8(v___x_2965_, sizeof(void*)*2, v_phase_2950_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_a_2960_);
v___x_2967_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_2964_, v___x_2966_, v_kind_2949_, v_a_2951_, v_a_2952_);
return v___x_2967_;
}
else
{
lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec(v_a_2962_);
lean_dec(v_a_2960_);
v___x_2968_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1);
v___x_2969_ = 0;
v___x_2970_ = l_Lean_MessageData_ofConstName(v_declName_2948_, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2968_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2973_, v_a_2951_, v_a_2952_);
return v___x_2974_;
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_declName_2948_);
v_a_2975_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2977_ = v___x_2959_;
v_isShared_2978_ = v_isSharedCheck_2986_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2959_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2986_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2979_ = lean_io_error_to_string(v_a_2975_);
v___x_2980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
v___x_2981_ = l_Lean_MessageData_ofFormat(v___x_2980_);
lean_inc(v_ref_2957_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_ref_2957_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2982_);
v___x_2984_ = v___x_2977_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object* v_declName_2987_, lean_object* v_kind_2988_, lean_object* v_phase_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
uint8_t v_kind_boxed_2993_; uint8_t v_phase_boxed_2994_; lean_object* v_res_2995_; 
v_kind_boxed_2993_ = lean_unbox(v_kind_2988_);
v_phase_boxed_2994_ = lean_unbox(v_phase_2989_);
v_res_2995_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2987_, v_kind_boxed_2993_, v_phase_boxed_2994_, v_a_2990_, v_a_2991_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object* v_stx_3008_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = l_Lean_Syntax_isNone(v_stx_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v_inner_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3010_ = lean_unsigned_to_nat(0u);
v_inner_3011_ = l_Lean_Syntax_getArg(v_stx_3008_, v___x_3010_);
v___x_3012_ = l_Lean_Syntax_getKind(v_inner_3011_);
v___x_3013_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2));
v___x_3014_ = lean_name_eq(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3015_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4));
v___x_3016_ = lean_name_eq(v___x_3012_, v___x_3015_);
lean_dec(v___x_3012_);
if (v___x_3016_ == 0)
{
uint8_t v___x_3017_; 
v___x_3017_ = 2;
return v___x_3017_;
}
else
{
uint8_t v___x_3018_; 
v___x_3018_ = 1;
return v___x_3018_;
}
}
else
{
uint8_t v___x_3019_; 
lean_dec(v___x_3012_);
v___x_3019_ = 0;
return v___x_3019_;
}
}
else
{
uint8_t v___x_3020_; 
v___x_3020_ = 2;
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object* v_stx_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_3021_);
lean_dec(v_stx_3021_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_3028_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
lean_ctor_set(v___x_3028_, 2, v___x_3027_);
lean_ctor_set(v___x_3028_, 3, v___x_3027_);
lean_ctor_set(v___x_3028_, 4, v___x_3027_);
lean_ctor_set(v___x_3028_, 5, v___x_3027_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_unsigned_to_nat(32u);
v___x_3030_ = lean_mk_empty_array_with_capacity(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4(void){
_start:
{
size_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3032_ = ((size_t)5ULL);
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = lean_unsigned_to_nat(32u);
v___x_3035_ = lean_mk_empty_array_with_capacity(v___x_3034_);
v___x_3036_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3);
v___x_3037_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
lean_ctor_set(v___x_3037_, 2, v___x_3033_);
lean_ctor_set(v___x_3037_, 3, v___x_3033_);
lean_ctor_set_usize(v___x_3037_, 4, v___x_3032_);
return v___x_3037_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_3039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
lean_ctor_set(v___x_3039_, 2, v___x_3038_);
lean_ctor_set(v___x_3039_, 3, v___x_3038_);
lean_ctor_set(v___x_3039_, 4, v___x_3038_);
return v___x_3039_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3040_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5);
v___x_3041_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4);
v___x_3042_ = lean_box(1);
v___x_3043_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2);
v___x_3044_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_3045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3043_);
lean_ctor_set(v___x_3045_, 2, v___x_3042_);
lean_ctor_set(v___x_3045_, 3, v___x_3041_);
lean_ctor_set(v___x_3045_, 4, v___x_3040_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object* v_declName_3046_, lean_object* v_stx_3047_, uint8_t v_attrKind_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1));
lean_inc(v_declName_3046_);
v___x_3053_ = l_Lean_ensureAttrDeclIsMeta(v___x_3052_, v_declName_3046_, v_attrKind_3048_, v_a_3049_, v_a_3050_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; 
lean_dec_ref_known(v___x_3053_, 1);
v___x_3054_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_3055_ = lean_st_mk_ref(v___x_3054_);
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = l_Lean_Syntax_getArg(v_stx_3047_, v___x_3056_);
v___x_3058_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_3057_);
lean_dec(v___x_3057_);
v___x_3059_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_3046_, v_attrKind_3048_, v___x_3058_, v_a_3049_, v_a_3050_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3068_; 
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v___x_3059_, 0);
lean_dec(v_unused_3069_);
v___x_3061_ = v___x_3059_;
v_isShared_3062_ = v_isSharedCheck_3068_;
goto v_resetjp_3060_;
}
else
{
lean_dec(v___x_3059_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3068_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3066_; 
v___x_3063_ = lean_st_ref_get(v___x_3055_);
lean_dec(v___x_3055_);
lean_dec(v___x_3063_);
v___x_3064_ = lean_box(0);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3064_);
v___x_3066_ = v___x_3061_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
else
{
lean_dec(v___x_3055_);
return v___x_3059_;
}
}
else
{
lean_dec(v_declName_3046_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object* v_declName_3070_, lean_object* v_stx_3071_, lean_object* v_attrKind_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
uint8_t v_attrKind_boxed_3076_; lean_object* v_res_3077_; 
v_attrKind_boxed_3076_ = lean_unbox(v_attrKind_3072_);
v_res_3077_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_3070_, v_stx_3071_, v_attrKind_boxed_3076_, v_a_3073_, v_a_3074_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_stx_3071_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object* v_ref_3080_, lean_object* v_declName_3081_, uint8_t v_phase_3082_, lean_object* v_proc_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_keys_3087_; lean_object* v___x_3088_; 
v___x_3085_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_3086_ = lean_st_ref_get(v___x_3085_);
v_keys_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_ref(v_keys_3087_);
lean_dec(v___x_3086_);
v___x_3088_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_3087_, v_declName_3081_);
lean_dec_ref(v_keys_3087_);
if (lean_obj_tag(v___x_3088_) == 1)
{
lean_object* v_val_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3099_; 
v_val_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_val_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3093_ = lean_st_ref_take(v_ref_3080_);
v___x_3094_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v___x_3093_, v_val_3089_, v_declName_3081_, v_phase_3082_, v_proc_3083_);
v___x_3095_ = lean_st_ref_put(v_ref_3080_, v___x_3094_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set_tag(v___x_3091_, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3095_);
v___x_3097_ = v___x_3091_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_dec(v___x_3088_);
lean_dec_ref(v_proc_3083_);
v___x_3100_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0));
v___x_3101_ = l_Lean_privateToUserName(v_declName_3081_);
v___x_3102_ = 1;
v___x_3103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3101_, v___x_3102_);
v___x_3104_ = lean_string_append(v___x_3100_, v___x_3103_);
lean_dec_ref(v___x_3103_);
v___x_3105_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1));
v___x_3106_ = lean_string_append(v___x_3104_, v___x_3105_);
v___x_3107_ = lean_mk_io_user_error(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object* v_ref_3109_, lean_object* v_declName_3110_, lean_object* v_phase_3111_, lean_object* v_proc_3112_, lean_object* v_a_3113_){
_start:
{
uint8_t v_phase_boxed_3114_; lean_object* v_res_3115_; 
v_phase_boxed_3114_ = lean_unbox(v_phase_3111_);
v_res_3115_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_3109_, v_declName_3110_, v_phase_boxed_3114_, v_proc_3112_);
lean_dec(v_ref_3109_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object* v_declName_3116_, uint8_t v_phase_3117_, lean_object* v_proc_3118_){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___x_3121_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v___x_3120_, v_declName_3116_, v_phase_3117_, v_proc_3118_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object* v_declName_3122_, lean_object* v_phase_3123_, lean_object* v_proc_3124_, lean_object* v_a_3125_){
_start:
{
uint8_t v_phase_boxed_3126_; lean_object* v_res_3127_; 
v_phase_boxed_3126_ = lean_unbox(v_phase_3123_);
v_res_3127_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_3122_, v_phase_boxed_3126_, v_proc_3124_);
return v_res_3127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_box(0);
v___x_3136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1));
v___x_3137_ = l_Lean_mkConst(v___x_3136_, v___x_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object* v_declName_3141_, lean_object* v_stx_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v_phase_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___y_3153_; 
v___x_3146_ = lean_unsigned_to_nat(1u);
v___x_3147_ = l_Lean_Syntax_getArg(v_stx_3142_, v___x_3146_);
v_phase_3148_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_3147_);
lean_dec(v___x_3147_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
lean_inc(v_declName_3141_);
v___x_3151_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3141_);
switch(v_phase_3148_)
{
case 0:
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
v___y_3153_ = v___x_3185_;
goto v___jp_3152_;
}
case 1:
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
v___y_3153_ = v___x_3186_;
goto v___jp_3152_;
}
default: 
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
v___y_3153_ = v___x_3187_;
goto v___jp_3152_;
}
}
v___jp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3154_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_3155_ = lean_st_mk_ref(v___x_3154_);
lean_inc(v_declName_3141_);
v___x_3156_ = l_Lean_mkConst(v_declName_3141_, v___x_3149_);
v___x_3157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4));
v___x_3158_ = l_Lean_Name_append(v_declName_3141_, v___x_3157_);
v___x_3159_ = l_Lean_Core_mkFreshUserName(v___x_3158_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v_val_3166_; lean_object* v___x_3167_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_unsigned_to_nat(3u);
v___x_3162_ = lean_mk_empty_array_with_capacity(v___x_3161_);
v___x_3163_ = lean_array_push(v___x_3162_, v___x_3151_);
lean_inc_ref(v___y_3153_);
v___x_3164_ = lean_array_push(v___x_3163_, v___y_3153_);
v___x_3165_ = lean_array_push(v___x_3164_, v___x_3156_);
v_val_3166_ = l_Lean_mkAppN(v___x_3150_, v___x_3165_);
lean_dec_ref(v___x_3165_);
v___x_3167_ = l_Lean_declareBuiltin(v_a_3160_, v_val_3166_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3176_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = lean_st_ref_get(v___x_3155_);
lean_dec(v___x_3155_);
lean_dec(v___x_3172_);
if (v_isShared_3171_ == 0)
{
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3168_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
else
{
lean_dec(v___x_3155_);
return v___x_3167_;
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v___x_3156_);
lean_dec(v___x_3155_);
lean_dec_ref(v___x_3151_);
v_a_3177_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3159_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3159_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object* v_declName_3188_, lean_object* v_stx_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3188_, v_stx_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_stx_3189_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3280_ = l_Lean_registerBuiltinAttribute(v___x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_declName_3283_, lean_object* v_stx_3284_, uint8_t v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3283_, v_stx_3284_, v___y_3286_, v___y_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_declName_3290_, lean_object* v_stx_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v_x_116__boxed_3296_; lean_object* v_res_3297_; 
v_x_116__boxed_3296_ = lean_unbox(v_x_3292_);
v_res_3297_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3290_, v_stx_3291_, v_x_116__boxed_3296_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v_stx_3291_);
return v_res_3297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_x_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3306_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3305_, v___y_3302_, v___y_3303_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v_x_3307_);
return v_res_3311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_unsigned_to_nat(3124561870u);
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3316_ = l_Lean_Name_num___override(v___x_3315_, v___x_3314_);
return v___x_3316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3319_ = l_Lean_Name_str___override(v___x_3318_, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3322_ = l_Lean_Name_str___override(v___x_3321_, v___x_3320_);
return v___x_3322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_unsigned_to_nat(2u);
v___x_3324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3325_ = l_Lean_Name_num___override(v___x_3324_, v___x_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3330_ = 1;
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3334_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___x_3332_);
lean_ctor_set(v___x_3334_, 2, v___x_3331_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*3, v___x_3330_);
return v___x_3334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___f_3335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___f_3336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___f_3336_);
lean_ctor_set(v___x_3338_, 2, v___f_3335_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3341_ = l_Lean_registerBuiltinAttribute(v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_a_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object* v_a_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v_env_3347_; lean_object* v___x_3348_; lean_object* v_ext_3349_; lean_object* v_toEnvExtension_3350_; lean_object* v_asyncMode_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3346_ = lean_st_ref_get(v_a_3344_);
v_env_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_ref(v_env_3347_);
lean_dec(v___x_3346_);
v___x_3348_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_3349_ = lean_ctor_get(v___x_3348_, 1);
v_toEnvExtension_3350_ = lean_ctor_get(v_ext_3349_, 0);
v_asyncMode_3351_ = lean_ctor_get(v_toEnvExtension_3350_, 2);
v___x_3352_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_3353_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3352_, v___x_3348_, v_env_3347_, v_asyncMode_3351_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object* v_a_3355_, lean_object* v_a_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3355_);
lean_dec(v_a_3355_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3365_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_unsigned_to_nat(32u);
v___x_3367_ = lean_mk_empty_array_with_capacity(v___x_3366_);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3369_ = ((size_t)5ULL);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_unsigned_to_nat(32u);
v___x_3372_ = lean_mk_empty_array_with_capacity(v___x_3371_);
v___x_3373_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0);
v___x_3374_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___x_3372_);
lean_ctor_set(v___x_3374_, 2, v___x_3370_);
lean_ctor_set(v___x_3374_, 3, v___x_3370_);
lean_ctor_set_usize(v___x_3374_, 4, v___x_3369_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v_traceState_3378_; lean_object* v_traces_3379_; lean_object* v___x_3380_; lean_object* v_traceState_3381_; lean_object* v_env_3382_; lean_object* v_nextMacroScope_3383_; lean_object* v_ngen_3384_; lean_object* v_auxDeclNGen_3385_; lean_object* v_cache_3386_; lean_object* v_messages_3387_; lean_object* v_infoState_3388_; lean_object* v_snapshotTasks_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3408_; 
v___x_3377_ = lean_st_ref_get(v___y_3375_);
v_traceState_3378_ = lean_ctor_get(v___x_3377_, 4);
lean_inc_ref(v_traceState_3378_);
lean_dec(v___x_3377_);
v_traces_3379_ = lean_ctor_get(v_traceState_3378_, 0);
lean_inc_ref(v_traces_3379_);
lean_dec_ref(v_traceState_3378_);
v___x_3380_ = lean_st_ref_take(v___y_3375_);
v_traceState_3381_ = lean_ctor_get(v___x_3380_, 4);
v_env_3382_ = lean_ctor_get(v___x_3380_, 0);
v_nextMacroScope_3383_ = lean_ctor_get(v___x_3380_, 1);
v_ngen_3384_ = lean_ctor_get(v___x_3380_, 2);
v_auxDeclNGen_3385_ = lean_ctor_get(v___x_3380_, 3);
v_cache_3386_ = lean_ctor_get(v___x_3380_, 5);
v_messages_3387_ = lean_ctor_get(v___x_3380_, 6);
v_infoState_3388_ = lean_ctor_get(v___x_3380_, 7);
v_snapshotTasks_3389_ = lean_ctor_get(v___x_3380_, 8);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3391_ = v___x_3380_;
v_isShared_3392_ = v_isSharedCheck_3408_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_snapshotTasks_3389_);
lean_inc(v_infoState_3388_);
lean_inc(v_messages_3387_);
lean_inc(v_cache_3386_);
lean_inc(v_traceState_3381_);
lean_inc(v_auxDeclNGen_3385_);
lean_inc(v_ngen_3384_);
lean_inc(v_nextMacroScope_3383_);
lean_inc(v_env_3382_);
lean_dec(v___x_3380_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3408_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
uint64_t v_tid_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3406_; 
v_tid_3393_ = lean_ctor_get_uint64(v_traceState_3381_, sizeof(void*)*1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_traceState_3381_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_traceState_3381_, 0);
lean_dec(v_unused_3407_);
v___x_3395_ = v_traceState_3381_;
v_isShared_3396_ = v_isSharedCheck_3406_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v_traceState_3381_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3406_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3397_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3397_);
v___x_3399_ = v___x_3395_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3397_);
lean_ctor_set_uint64(v_reuseFailAlloc_3405_, sizeof(void*)*1, v_tid_3393_);
v___x_3399_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3401_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 4, v___x_3399_);
v___x_3401_ = v___x_3391_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_env_3382_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_nextMacroScope_3383_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_ngen_3384_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_auxDeclNGen_3385_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3404_, 5, v_cache_3386_);
lean_ctor_set(v_reuseFailAlloc_3404_, 6, v_messages_3387_);
lean_ctor_set(v_reuseFailAlloc_3404_, 7, v_infoState_3388_);
lean_ctor_set(v_reuseFailAlloc_3404_, 8, v_snapshotTasks_3389_);
v___x_3401_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_st_ref_put(v___y_3375_, v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_traces_3379_);
return v___x_3403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3409_);
lean_dec(v___y_3409_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3420_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
return v_res_3433_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object* v_opts_3434_, lean_object* v_opt_3435_){
_start:
{
lean_object* v_name_3436_; lean_object* v_defValue_3437_; lean_object* v_map_3438_; lean_object* v___x_3439_; 
v_name_3436_ = lean_ctor_get(v_opt_3435_, 0);
v_defValue_3437_ = lean_ctor_get(v_opt_3435_, 1);
v_map_3438_ = lean_ctor_get(v_opts_3434_, 0);
v___x_3439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3438_, v_name_3436_);
if (lean_obj_tag(v___x_3439_) == 0)
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_unbox(v_defValue_3437_);
return v___x_3440_;
}
else
{
lean_object* v_val_3441_; 
v_val_3441_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v___x_3439_, 1);
if (lean_obj_tag(v_val_3441_) == 1)
{
uint8_t v_v_3442_; 
v_v_3442_ = lean_ctor_get_uint8(v_val_3441_, 0);
lean_dec_ref_known(v_val_3441_, 0);
return v_v_3442_;
}
else
{
uint8_t v___x_3443_; 
lean_dec(v_val_3441_);
v___x_3443_ = lean_unbox(v_defValue_3437_);
return v___x_3443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object* v_opts_3444_, lean_object* v_opt_3445_){
_start:
{
uint8_t v_res_3446_; lean_object* v_r_3447_; 
v_res_3446_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3444_, v_opt_3445_);
lean_dec_ref(v_opt_3445_);
lean_dec_ref(v_opts_3444_);
v_r_3447_ = lean_box(v_res_3446_);
return v_r_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t v___x_3448_, lean_object* v_e_3449_, lean_object* v_snd_3450_, lean_object* v_proc_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
if (v___x_3448_ == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_3449_, v_snd_3450_, v_proc_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
return v___x_3462_;
}
else
{
lean_object* v___x_3463_; 
lean_inc(v___y_3460_);
lean_inc_ref(v___y_3459_);
lean_inc(v___y_3458_);
lean_inc_ref(v___y_3457_);
lean_inc(v___y_3456_);
lean_inc_ref(v___y_3455_);
lean_inc(v___y_3454_);
lean_inc_ref(v___y_3453_);
lean_inc(v___y_3452_);
v___x_3463_ = lean_apply_11(v_proc_3451_, v_e_3449_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, lean_box(0));
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object* v___x_3464_, lean_object* v_e_3465_, lean_object* v_snd_3466_, lean_object* v_proc_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v___x_59314__boxed_3478_; lean_object* v_res_3479_; 
v___x_59314__boxed_3478_ = lean_unbox(v___x_3464_);
v_res_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_59314__boxed_3478_, v_e_3465_, v_snd_3466_, v_proc_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec(v_snd_3466_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t v_sz_3480_, size_t v_i_3481_, lean_object* v_bs_3482_){
_start:
{
uint8_t v___x_3483_; 
v___x_3483_ = lean_usize_dec_lt(v_i_3481_, v_sz_3480_);
if (v___x_3483_ == 0)
{
return v_bs_3482_;
}
else
{
lean_object* v_v_3484_; lean_object* v_msg_3485_; lean_object* v___x_3486_; lean_object* v_bs_x27_3487_; size_t v___x_3488_; size_t v___x_3489_; lean_object* v___x_3490_; 
v_v_3484_ = lean_array_uget_borrowed(v_bs_3482_, v_i_3481_);
v_msg_3485_ = lean_ctor_get(v_v_3484_, 1);
lean_inc_ref(v_msg_3485_);
v___x_3486_ = lean_unsigned_to_nat(0u);
v_bs_x27_3487_ = lean_array_uset(v_bs_3482_, v_i_3481_, v___x_3486_);
v___x_3488_ = ((size_t)1ULL);
v___x_3489_ = lean_usize_add(v_i_3481_, v___x_3488_);
v___x_3490_ = lean_array_uset(v_bs_x27_3487_, v_i_3481_, v_msg_3485_);
v_i_3481_ = v___x_3489_;
v_bs_3482_ = v___x_3490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_3492_, lean_object* v_i_3493_, lean_object* v_bs_3494_){
_start:
{
size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3492_);
lean_dec(v_sz_3492_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3493_);
lean_dec(v_i_3493_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_boxed_3495_, v_i_boxed_3496_, v_bs_3494_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object* v_msgData_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v___x_3504_; lean_object* v_env_3505_; lean_object* v___x_3506_; lean_object* v_mctx_3507_; lean_object* v_lctx_3508_; lean_object* v_options_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3504_ = lean_st_ref_get(v___y_3502_);
v_env_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc_ref(v_env_3505_);
lean_dec(v___x_3504_);
v___x_3506_ = lean_st_ref_get(v___y_3500_);
v_mctx_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc_ref(v_mctx_3507_);
lean_dec(v___x_3506_);
v_lctx_3508_ = lean_ctor_get(v___y_3499_, 2);
v_options_3509_ = lean_ctor_get(v___y_3501_, 2);
lean_inc_ref(v_options_3509_);
lean_inc_ref(v_lctx_3508_);
v___x_3510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3510_, 0, v_env_3505_);
lean_ctor_set(v___x_3510_, 1, v_mctx_3507_);
lean_ctor_set(v___x_3510_, 2, v_lctx_3508_);
lean_ctor_set(v___x_3510_, 3, v_options_3509_);
v___x_3511_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v_msgData_3498_);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msgData_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object* v_oldTraces_3520_, lean_object* v_data_3521_, lean_object* v_ref_3522_, lean_object* v_msg_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_fileName_3529_; lean_object* v_fileMap_3530_; lean_object* v_options_3531_; lean_object* v_currRecDepth_3532_; lean_object* v_maxRecDepth_3533_; lean_object* v_ref_3534_; lean_object* v_currNamespace_3535_; lean_object* v_openDecls_3536_; lean_object* v_initHeartbeats_3537_; lean_object* v_maxHeartbeats_3538_; lean_object* v_quotContext_3539_; lean_object* v_currMacroScope_3540_; uint8_t v_diag_3541_; lean_object* v_cancelTk_x3f_3542_; uint8_t v_suppressElabErrors_3543_; lean_object* v_inheritedTraceOptions_3544_; lean_object* v___x_3545_; lean_object* v_traceState_3546_; lean_object* v_traces_3547_; lean_object* v_ref_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; size_t v_sz_3551_; size_t v___x_3552_; lean_object* v___x_3553_; lean_object* v_msg_3554_; lean_object* v___x_3555_; lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3593_; 
v_fileName_3529_ = lean_ctor_get(v___y_3526_, 0);
v_fileMap_3530_ = lean_ctor_get(v___y_3526_, 1);
v_options_3531_ = lean_ctor_get(v___y_3526_, 2);
v_currRecDepth_3532_ = lean_ctor_get(v___y_3526_, 3);
v_maxRecDepth_3533_ = lean_ctor_get(v___y_3526_, 4);
v_ref_3534_ = lean_ctor_get(v___y_3526_, 5);
v_currNamespace_3535_ = lean_ctor_get(v___y_3526_, 6);
v_openDecls_3536_ = lean_ctor_get(v___y_3526_, 7);
v_initHeartbeats_3537_ = lean_ctor_get(v___y_3526_, 8);
v_maxHeartbeats_3538_ = lean_ctor_get(v___y_3526_, 9);
v_quotContext_3539_ = lean_ctor_get(v___y_3526_, 10);
v_currMacroScope_3540_ = lean_ctor_get(v___y_3526_, 11);
v_diag_3541_ = lean_ctor_get_uint8(v___y_3526_, sizeof(void*)*14);
v_cancelTk_x3f_3542_ = lean_ctor_get(v___y_3526_, 12);
v_suppressElabErrors_3543_ = lean_ctor_get_uint8(v___y_3526_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3544_ = lean_ctor_get(v___y_3526_, 13);
v___x_3545_ = lean_st_ref_get(v___y_3527_);
v_traceState_3546_ = lean_ctor_get(v___x_3545_, 4);
lean_inc_ref(v_traceState_3546_);
lean_dec(v___x_3545_);
v_traces_3547_ = lean_ctor_get(v_traceState_3546_, 0);
lean_inc_ref(v_traces_3547_);
lean_dec_ref(v_traceState_3546_);
v_ref_3548_ = l_Lean_replaceRef(v_ref_3522_, v_ref_3534_);
lean_inc_ref(v_inheritedTraceOptions_3544_);
lean_inc(v_cancelTk_x3f_3542_);
lean_inc(v_currMacroScope_3540_);
lean_inc(v_quotContext_3539_);
lean_inc(v_maxHeartbeats_3538_);
lean_inc(v_initHeartbeats_3537_);
lean_inc(v_openDecls_3536_);
lean_inc(v_currNamespace_3535_);
lean_inc(v_maxRecDepth_3533_);
lean_inc(v_currRecDepth_3532_);
lean_inc_ref(v_options_3531_);
lean_inc_ref(v_fileMap_3530_);
lean_inc_ref(v_fileName_3529_);
v___x_3549_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3549_, 0, v_fileName_3529_);
lean_ctor_set(v___x_3549_, 1, v_fileMap_3530_);
lean_ctor_set(v___x_3549_, 2, v_options_3531_);
lean_ctor_set(v___x_3549_, 3, v_currRecDepth_3532_);
lean_ctor_set(v___x_3549_, 4, v_maxRecDepth_3533_);
lean_ctor_set(v___x_3549_, 5, v_ref_3548_);
lean_ctor_set(v___x_3549_, 6, v_currNamespace_3535_);
lean_ctor_set(v___x_3549_, 7, v_openDecls_3536_);
lean_ctor_set(v___x_3549_, 8, v_initHeartbeats_3537_);
lean_ctor_set(v___x_3549_, 9, v_maxHeartbeats_3538_);
lean_ctor_set(v___x_3549_, 10, v_quotContext_3539_);
lean_ctor_set(v___x_3549_, 11, v_currMacroScope_3540_);
lean_ctor_set(v___x_3549_, 12, v_cancelTk_x3f_3542_);
lean_ctor_set(v___x_3549_, 13, v_inheritedTraceOptions_3544_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*14, v_diag_3541_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*14 + 1, v_suppressElabErrors_3543_);
v___x_3550_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3547_);
lean_dec_ref(v_traces_3547_);
v_sz_3551_ = lean_array_size(v___x_3550_);
v___x_3552_ = ((size_t)0ULL);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_3551_, v___x_3552_, v___x_3550_);
v_msg_3554_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3554_, 0, v_data_3521_);
lean_ctor_set(v_msg_3554_, 1, v_msg_3523_);
lean_ctor_set(v_msg_3554_, 2, v___x_3553_);
v___x_3555_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msg_3554_, v___y_3524_, v___y_3525_, v___x_3549_, v___y_3527_);
lean_dec_ref_known(v___x_3549_, 14);
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3593_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3593_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v_traceState_3561_; lean_object* v_env_3562_; lean_object* v_nextMacroScope_3563_; lean_object* v_ngen_3564_; lean_object* v_auxDeclNGen_3565_; lean_object* v_cache_3566_; lean_object* v_messages_3567_; lean_object* v_infoState_3568_; lean_object* v_snapshotTasks_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3592_; 
v___x_3560_ = lean_st_ref_take(v___y_3527_);
v_traceState_3561_ = lean_ctor_get(v___x_3560_, 4);
v_env_3562_ = lean_ctor_get(v___x_3560_, 0);
v_nextMacroScope_3563_ = lean_ctor_get(v___x_3560_, 1);
v_ngen_3564_ = lean_ctor_get(v___x_3560_, 2);
v_auxDeclNGen_3565_ = lean_ctor_get(v___x_3560_, 3);
v_cache_3566_ = lean_ctor_get(v___x_3560_, 5);
v_messages_3567_ = lean_ctor_get(v___x_3560_, 6);
v_infoState_3568_ = lean_ctor_get(v___x_3560_, 7);
v_snapshotTasks_3569_ = lean_ctor_get(v___x_3560_, 8);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3571_ = v___x_3560_;
v_isShared_3572_ = v_isSharedCheck_3592_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_snapshotTasks_3569_);
lean_inc(v_infoState_3568_);
lean_inc(v_messages_3567_);
lean_inc(v_cache_3566_);
lean_inc(v_traceState_3561_);
lean_inc(v_auxDeclNGen_3565_);
lean_inc(v_ngen_3564_);
lean_inc(v_nextMacroScope_3563_);
lean_inc(v_env_3562_);
lean_dec(v___x_3560_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3592_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
uint64_t v_tid_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3590_; 
v_tid_3573_ = lean_ctor_get_uint64(v_traceState_3561_, sizeof(void*)*1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_traceState_3561_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; 
v_unused_3591_ = lean_ctor_get(v_traceState_3561_, 0);
lean_dec(v_unused_3591_);
v___x_3575_ = v_traceState_3561_;
v_isShared_3576_ = v_isSharedCheck_3590_;
goto v_resetjp_3574_;
}
else
{
lean_dec(v_traceState_3561_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3590_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v_ref_3522_);
lean_ctor_set(v___x_3577_, 1, v_a_3556_);
v___x_3578_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3520_, v___x_3577_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3578_);
v___x_3580_ = v___x_3575_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3578_);
lean_ctor_set_uint64(v_reuseFailAlloc_3589_, sizeof(void*)*1, v_tid_3573_);
v___x_3580_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3582_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 4, v___x_3580_);
v___x_3582_ = v___x_3571_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_env_3562_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_nextMacroScope_3563_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_ngen_3564_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_auxDeclNGen_3565_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3588_, 5, v_cache_3566_);
lean_ctor_set(v_reuseFailAlloc_3588_, 6, v_messages_3567_);
lean_ctor_set(v_reuseFailAlloc_3588_, 7, v_infoState_3568_);
lean_ctor_set(v_reuseFailAlloc_3588_, 8, v_snapshotTasks_3569_);
v___x_3582_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3583_ = lean_st_ref_put(v___y_3527_, v___x_3582_);
v___x_3584_ = lean_box(0);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3584_);
v___x_3586_ = v___x_3558_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_3594_, lean_object* v_data_3595_, lean_object* v_ref_3596_, lean_object* v_msg_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3594_, v_data_3595_, v_ref_3596_, v_msg_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object* v_x_3604_){
_start:
{
if (lean_obj_tag(v_x_3604_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_a_3606_ = lean_ctor_get(v_x_3604_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_x_3604_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v_x_3604_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v_x_3604_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 1);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
v_a_3614_ = lean_ctor_get(v_x_3604_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_x_3604_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v_x_3604_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v_x_3604_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 0);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object* v_x_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object* v_opts_3625_, lean_object* v_opt_3626_){
_start:
{
lean_object* v_name_3627_; lean_object* v_defValue_3628_; lean_object* v_map_3629_; lean_object* v___x_3630_; 
v_name_3627_ = lean_ctor_get(v_opt_3626_, 0);
v_defValue_3628_ = lean_ctor_get(v_opt_3626_, 1);
v_map_3629_ = lean_ctor_get(v_opts_3625_, 0);
v___x_3630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3629_, v_name_3627_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_inc(v_defValue_3628_);
return v_defValue_3628_;
}
else
{
lean_object* v_val_3631_; 
v_val_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_val_3631_);
lean_dec_ref_known(v___x_3630_, 1);
if (lean_obj_tag(v_val_3631_) == 3)
{
lean_object* v_v_3632_; 
v_v_3632_ = lean_ctor_get(v_val_3631_, 0);
lean_inc(v_v_3632_);
lean_dec_ref_known(v_val_3631_, 1);
return v_v_3632_;
}
else
{
lean_dec(v_val_3631_);
lean_inc(v_defValue_3628_);
return v_defValue_3628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object* v_opts_3633_, lean_object* v_opt_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3633_, v_opt_3634_);
lean_dec_ref(v_opt_3634_);
lean_dec_ref(v_opts_3633_);
return v_res_3635_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object* v_e_3636_){
_start:
{
if (lean_obj_tag(v_e_3636_) == 0)
{
uint8_t v___x_3637_; 
v___x_3637_ = 2;
return v___x_3637_;
}
else
{
uint8_t v___x_3638_; 
v___x_3638_ = 0;
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object* v_e_3639_){
_start:
{
uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_e_3639_);
lean_dec_ref(v_e_3639_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3642_; double v___x_3643_; 
v___x_3642_ = lean_unsigned_to_nat(0u);
v___x_3643_ = lean_float_of_nat(v___x_3642_);
return v___x_3643_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1));
v___x_3646_ = l_Lean_stringToMessageData(v___x_3645_);
return v___x_3646_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3647_; double v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(1000u);
v___x_3648_ = lean_float_of_nat(v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object* v_cls_3649_, uint8_t v_collapsed_3650_, lean_object* v_tag_3651_, lean_object* v_opts_3652_, uint8_t v_clsEnabled_3653_, lean_object* v_oldTraces_3654_, lean_object* v_msg_3655_, lean_object* v_resStartStop_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_fst_3667_; lean_object* v_snd_3668_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v_data_3672_; lean_object* v_fst_3683_; lean_object* v_snd_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___y_3688_; lean_object* v_a_3689_; uint8_t v___y_3704_; double v___y_3735_; 
v_fst_3667_ = lean_ctor_get(v_resStartStop_3656_, 0);
lean_inc(v_fst_3667_);
v_snd_3668_ = lean_ctor_get(v_resStartStop_3656_, 1);
lean_inc(v_snd_3668_);
lean_dec_ref(v_resStartStop_3656_);
v_fst_3683_ = lean_ctor_get(v_snd_3668_, 0);
lean_inc(v_fst_3683_);
v_snd_3684_ = lean_ctor_get(v_snd_3668_, 1);
lean_inc(v_snd_3684_);
lean_dec(v_snd_3668_);
v___x_3685_ = l_Lean_trace_profiler;
v___x_3686_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3652_, v___x_3685_);
if (v___x_3686_ == 0)
{
v___y_3704_ = v___x_3686_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3740_; uint8_t v___x_3741_; 
v___x_3740_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3741_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3652_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3743_; double v___x_3744_; double v___x_3745_; double v___x_3746_; 
v___x_3742_ = l_Lean_trace_profiler_threshold;
v___x_3743_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3652_, v___x_3742_);
v___x_3744_ = lean_float_of_nat(v___x_3743_);
v___x_3745_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3);
v___x_3746_ = lean_float_div(v___x_3744_, v___x_3745_);
v___y_3735_ = v___x_3746_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; double v___x_3749_; 
v___x_3747_ = l_Lean_trace_profiler_threshold;
v___x_3748_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3652_, v___x_3747_);
v___x_3749_ = lean_float_of_nat(v___x_3748_);
v___y_3735_ = v___x_3749_;
goto v___jp_3734_;
}
}
v___jp_3669_:
{
lean_object* v___x_3673_; 
lean_inc(v___y_3671_);
v___x_3673_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3654_, v_data_3672_, v___y_3671_, v___y_3670_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v___x_3674_; 
lean_dec_ref_known(v___x_3673_, 1);
v___x_3674_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3667_);
return v___x_3674_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_fst_3667_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3673_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
v___jp_3687_:
{
uint8_t v_result_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; double v___x_3693_; lean_object* v_data_3694_; 
v_result_3690_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_fst_3667_);
v___x_3691_ = lean_box(v_result_3690_);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
v___x_3693_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0);
lean_inc_ref(v_tag_3651_);
lean_inc_ref(v___x_3692_);
lean_inc(v_cls_3649_);
v_data_3694_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3694_, 0, v_cls_3649_);
lean_ctor_set(v_data_3694_, 1, v___x_3692_);
lean_ctor_set(v_data_3694_, 2, v_tag_3651_);
lean_ctor_set_float(v_data_3694_, sizeof(void*)*3, v___x_3693_);
lean_ctor_set_float(v_data_3694_, sizeof(void*)*3 + 8, v___x_3693_);
lean_ctor_set_uint8(v_data_3694_, sizeof(void*)*3 + 16, v_collapsed_3650_);
if (v___x_3686_ == 0)
{
lean_dec_ref_known(v___x_3692_, 1);
lean_dec(v_snd_3684_);
lean_dec(v_fst_3683_);
lean_dec_ref(v_tag_3651_);
lean_dec(v_cls_3649_);
v___y_3670_ = v_a_3689_;
v___y_3671_ = v___y_3688_;
v_data_3672_ = v_data_3694_;
goto v___jp_3669_;
}
else
{
lean_object* v_data_3695_; double v___x_3696_; double v___x_3697_; 
lean_dec_ref_known(v_data_3694_, 3);
v_data_3695_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3695_, 0, v_cls_3649_);
lean_ctor_set(v_data_3695_, 1, v___x_3692_);
lean_ctor_set(v_data_3695_, 2, v_tag_3651_);
v___x_3696_ = lean_unbox_float(v_fst_3683_);
lean_dec(v_fst_3683_);
lean_ctor_set_float(v_data_3695_, sizeof(void*)*3, v___x_3696_);
v___x_3697_ = lean_unbox_float(v_snd_3684_);
lean_dec(v_snd_3684_);
lean_ctor_set_float(v_data_3695_, sizeof(void*)*3 + 8, v___x_3697_);
lean_ctor_set_uint8(v_data_3695_, sizeof(void*)*3 + 16, v_collapsed_3650_);
v___y_3670_ = v_a_3689_;
v___y_3671_ = v___y_3688_;
v_data_3672_ = v_data_3695_;
goto v___jp_3669_;
}
}
v___jp_3698_:
{
lean_object* v_ref_3699_; lean_object* v___x_3700_; 
v_ref_3699_ = lean_ctor_get(v___y_3664_, 5);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
lean_inc(v___y_3661_);
lean_inc_ref(v___y_3660_);
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc(v___y_3657_);
lean_inc(v_fst_3667_);
v___x_3700_ = lean_apply_11(v_msg_3655_, v_fst_3667_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___y_3688_ = v_ref_3699_;
v_a_3689_ = v_a_3701_;
goto v___jp_3687_;
}
else
{
lean_object* v___x_3702_; 
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2);
v___y_3688_ = v_ref_3699_;
v_a_3689_ = v___x_3702_;
goto v___jp_3687_;
}
}
v___jp_3703_:
{
if (v_clsEnabled_3653_ == 0)
{
if (v___y_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v_traceState_3706_; lean_object* v_env_3707_; lean_object* v_nextMacroScope_3708_; lean_object* v_ngen_3709_; lean_object* v_auxDeclNGen_3710_; lean_object* v_cache_3711_; lean_object* v_messages_3712_; lean_object* v_infoState_3713_; lean_object* v_snapshotTasks_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3733_; 
lean_dec(v_snd_3684_);
lean_dec(v_fst_3683_);
lean_dec_ref(v_msg_3655_);
lean_dec_ref(v_tag_3651_);
lean_dec(v_cls_3649_);
v___x_3705_ = lean_st_ref_take(v___y_3665_);
v_traceState_3706_ = lean_ctor_get(v___x_3705_, 4);
v_env_3707_ = lean_ctor_get(v___x_3705_, 0);
v_nextMacroScope_3708_ = lean_ctor_get(v___x_3705_, 1);
v_ngen_3709_ = lean_ctor_get(v___x_3705_, 2);
v_auxDeclNGen_3710_ = lean_ctor_get(v___x_3705_, 3);
v_cache_3711_ = lean_ctor_get(v___x_3705_, 5);
v_messages_3712_ = lean_ctor_get(v___x_3705_, 6);
v_infoState_3713_ = lean_ctor_get(v___x_3705_, 7);
v_snapshotTasks_3714_ = lean_ctor_get(v___x_3705_, 8);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3716_ = v___x_3705_;
v_isShared_3717_ = v_isSharedCheck_3733_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_snapshotTasks_3714_);
lean_inc(v_infoState_3713_);
lean_inc(v_messages_3712_);
lean_inc(v_cache_3711_);
lean_inc(v_traceState_3706_);
lean_inc(v_auxDeclNGen_3710_);
lean_inc(v_ngen_3709_);
lean_inc(v_nextMacroScope_3708_);
lean_inc(v_env_3707_);
lean_dec(v___x_3705_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3733_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint64_t v_tid_3718_; lean_object* v_traces_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3732_; 
v_tid_3718_ = lean_ctor_get_uint64(v_traceState_3706_, sizeof(void*)*1);
v_traces_3719_ = lean_ctor_get(v_traceState_3706_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_traceState_3706_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3721_ = v_traceState_3706_;
v_isShared_3722_ = v_isSharedCheck_3732_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_traces_3719_);
lean_dec(v_traceState_3706_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3732_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3723_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3654_, v_traces_3719_);
lean_dec_ref(v_traces_3719_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3723_);
v___x_3725_ = v___x_3721_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3723_);
lean_ctor_set_uint64(v_reuseFailAlloc_3731_, sizeof(void*)*1, v_tid_3718_);
v___x_3725_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v___x_3725_);
v___x_3727_ = v___x_3716_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_env_3707_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_nextMacroScope_3708_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_ngen_3709_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_auxDeclNGen_3710_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3730_, 5, v_cache_3711_);
lean_ctor_set(v_reuseFailAlloc_3730_, 6, v_messages_3712_);
lean_ctor_set(v_reuseFailAlloc_3730_, 7, v_infoState_3713_);
lean_ctor_set(v_reuseFailAlloc_3730_, 8, v_snapshotTasks_3714_);
v___x_3727_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_st_ref_put(v___y_3665_, v___x_3727_);
v___x_3729_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3667_);
return v___x_3729_;
}
}
}
}
}
else
{
goto v___jp_3698_;
}
}
else
{
goto v___jp_3698_;
}
}
v___jp_3734_:
{
double v___x_3736_; double v___x_3737_; double v___x_3738_; uint8_t v___x_3739_; 
v___x_3736_ = lean_unbox_float(v_snd_3684_);
v___x_3737_ = lean_unbox_float(v_fst_3683_);
v___x_3738_ = lean_float_sub(v___x_3736_, v___x_3737_);
v___x_3739_ = lean_float_decLt(v___y_3735_, v___x_3738_);
v___y_3704_ = v___x_3739_;
goto v___jp_3703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object** _args){
lean_object* v_cls_3750_ = _args[0];
lean_object* v_collapsed_3751_ = _args[1];
lean_object* v_tag_3752_ = _args[2];
lean_object* v_opts_3753_ = _args[3];
lean_object* v_clsEnabled_3754_ = _args[4];
lean_object* v_oldTraces_3755_ = _args[5];
lean_object* v_msg_3756_ = _args[6];
lean_object* v_resStartStop_3757_ = _args[7];
lean_object* v___y_3758_ = _args[8];
lean_object* v___y_3759_ = _args[9];
lean_object* v___y_3760_ = _args[10];
lean_object* v___y_3761_ = _args[11];
lean_object* v___y_3762_ = _args[12];
lean_object* v___y_3763_ = _args[13];
lean_object* v___y_3764_ = _args[14];
lean_object* v___y_3765_ = _args[15];
lean_object* v___y_3766_ = _args[16];
lean_object* v___y_3767_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3768_; uint8_t v_clsEnabled_boxed_3769_; lean_object* v_res_3770_; 
v_collapsed_boxed_3768_ = lean_unbox(v_collapsed_3751_);
v_clsEnabled_boxed_3769_ = lean_unbox(v_clsEnabled_3754_);
v_res_3770_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_3750_, v_collapsed_boxed_3768_, v_tag_3752_, v_opts_3753_, v_clsEnabled_boxed_3769_, v_oldTraces_3755_, v_msg_3756_, v_resStartStop_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v_opts_3753_);
return v_res_3770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0));
v___x_3773_ = l_Lean_stringToMessageData(v___x_3772_);
return v___x_3773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2));
v___x_3776_ = l_Lean_stringToMessageData(v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4));
v___x_3779_ = l_Lean_stringToMessageData(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6));
v___x_3782_ = l_Lean_stringToMessageData(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8));
v___x_3785_ = l_Lean_stringToMessageData(v___x_3784_);
return v___x_3785_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10));
v___x_3788_ = l_Lean_stringToMessageData(v___x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object* v___x_3789_, lean_object* v_e_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
if (lean_obj_tag(v_x_3791_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v_e_3790_);
v_a_3802_ = lean_ctor_get(v_x_3791_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_x_3791_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3804_ = v_x_3791_;
v_isShared_3805_ = v_isSharedCheck_3816_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v_x_3791_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3816_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3807_ = l_Lean_MessageData_ofName(v___x_3789_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_Lean_Exception_toMessageData(v_a_3802_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3812_);
v___x_3814_ = v___x_3804_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3855_; 
v_a_3817_ = lean_ctor_get(v_x_3791_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_x_3791_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3819_ = v_x_3791_;
v_isShared_3820_ = v_isSharedCheck_3855_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v_x_3791_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3855_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
if (lean_obj_tag(v_a_3817_) == 0)
{
uint8_t v_done_3821_; 
v_done_3821_ = lean_ctor_get_uint8(v_a_3817_, 0);
lean_dec_ref_known(v_a_3817_, 0);
if (v_done_3821_ == 1)
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3823_ = l_Lean_MessageData_ofName(v___x_3789_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = l_Lean_indentExpr(v_e_3790_);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3828_);
v___x_3830_ = v___x_3819_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
lean_dec_ref(v_e_3790_);
v___x_3832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3833_ = l_Lean_MessageData_ofName(v___x_3789_);
v___x_3834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3832_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7);
v___x_3836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3836_);
v___x_3838_ = v___x_3819_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
else
{
lean_object* v_e_x27_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3853_; 
v_e_x27_3840_ = lean_ctor_get(v_a_3817_, 0);
lean_inc_ref(v_e_x27_3840_);
lean_dec_ref_known(v_a_3817_, 2);
v___x_3841_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3842_ = l_Lean_MessageData_ofName(v___x_3789_);
v___x_3843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3841_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3843_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = l_Lean_indentExpr(v_e_3790_);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3847_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = l_Lean_indentExpr(v_e_x27_3840_);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3851_);
v___x_3853_ = v___x_3819_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object* v___x_3856_, lean_object* v_e_3857_, lean_object* v_x_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_3856_, v_e_3857_, v_x_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
return v_res_3869_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8));
v___x_3896_ = l_Lean_Name_append(v___x_3895_, v___x_3894_);
return v___x_3896_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10(void){
_start:
{
lean_object* v___x_3897_; double v___x_3898_; 
v___x_3897_ = lean_unsigned_to_nat(1000000000u);
v___x_3898_ = lean_float_of_nat(v___x_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object* v_erased_3899_, lean_object* v_e_3900_, lean_object* v_as_3901_, size_t v_sz_3902_, size_t v_i_3903_, lean_object* v_b_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_a_3916_; uint8_t v___x_3920_; 
v___x_3920_ = lean_usize_dec_lt(v_i_3903_, v_sz_3902_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
lean_dec_ref(v_e_3900_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v_b_3904_);
return v___x_3921_;
}
else
{
lean_object* v_a_3922_; lean_object* v_fst_3923_; lean_object* v_toCbvSimprocOLeanEntry_3924_; lean_object* v_snd_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_4066_; 
lean_dec_ref(v_b_3904_);
v_a_3922_ = lean_array_uget(v_as_3901_, v_i_3903_);
v_fst_3923_ = lean_ctor_get(v_a_3922_, 0);
lean_inc(v_fst_3923_);
v_toCbvSimprocOLeanEntry_3924_ = lean_ctor_get(v_fst_3923_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_3924_);
v_snd_3925_ = lean_ctor_get(v_a_3922_, 1);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_a_3922_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v_a_3922_, 0);
lean_dec(v_unused_4067_);
v___x_3927_ = v_a_3922_;
v_isShared_3928_ = v_isSharedCheck_4066_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_snd_3925_);
lean_dec(v_a_3922_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_4066_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v_proc_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_4064_; 
v_proc_3929_ = lean_ctor_get(v_fst_3923_, 1);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_fst_3923_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v_fst_3923_, 0);
lean_dec(v_unused_4065_);
v___x_3931_ = v_fst_3923_;
v_isShared_3932_ = v_isSharedCheck_4064_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_proc_3929_);
lean_dec(v_fst_3923_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_4064_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v_declName_3933_; lean_object* v___x_3934_; lean_object* v___y_3936_; lean_object* v___x_3942_; uint8_t v___x_3943_; lean_object* v___y_3945_; 
v_declName_3933_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_3924_, 0);
lean_inc(v_declName_3933_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_3924_);
v___x_3934_ = lean_box(0);
v___x_3942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v___x_3943_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_3899_, v_declName_3933_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3968_; lean_object* v_options_3969_; lean_object* v_inheritedTraceOptions_3970_; uint8_t v_hasTrace_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1));
v_options_3969_ = lean_ctor_get(v___y_3912_, 2);
v_inheritedTraceOptions_3970_ = lean_ctor_get(v___y_3912_, 13);
v_hasTrace_3971_ = lean_ctor_get_uint8(v_options_3969_, sizeof(void*)*1);
v___x_3972_ = lean_unsigned_to_nat(0u);
v___x_3973_ = lean_nat_dec_eq(v_snd_3925_, v___x_3972_);
if (v_hasTrace_3971_ == 0)
{
lean_object* v___x_3974_; 
lean_dec(v_declName_3933_);
lean_inc_ref(v_e_3900_);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3973_, v_e_3900_, v_snd_3925_, v_proc_3929_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v_snd_3925_);
v___y_3945_ = v___x_3974_;
goto v___jp_3944_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___f_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v_a_3988_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v_a_4003_; 
v___x_3975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2));
v___x_3976_ = l_Lean_privateToUserName(v_declName_3933_);
v___x_3977_ = lean_box(0);
v___x_3978_ = l_Lean_Name_replacePrefix(v___x_3976_, v___x_3968_, v___x_3977_);
v___x_3979_ = l_Lean_Name_replacePrefix(v___x_3978_, v___x_3975_, v___x_3977_);
lean_inc_ref(v_e_3900_);
v___f_3980_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed), 13, 2);
lean_closure_set(v___f_3980_, 0, v___x_3979_);
lean_closure_set(v___f_3980_, 1, v_e_3900_);
v___x_3981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6));
v___x_3983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9);
v___x_3984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3970_, v_options_3969_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_4061_; uint8_t v___x_4062_; 
v___x_4061_ = l_Lean_trace_profiler;
v___x_4062_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3969_, v___x_4061_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; 
lean_dec_ref(v___f_3980_);
lean_inc_ref(v_e_3900_);
v___x_4063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3973_, v_e_3900_, v_snd_3925_, v_proc_3929_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v_snd_3925_);
v___y_3945_ = v___x_4063_;
goto v___jp_3944_;
}
else
{
goto v___jp_4012_;
}
}
else
{
goto v___jp_4012_;
}
v___jp_3985_:
{
lean_object* v___x_3989_; double v___x_3990_; double v___x_3991_; double v___x_3992_; double v___x_3993_; double v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3989_ = lean_io_mono_nanos_now();
v___x_3990_ = lean_float_of_nat(v___y_3987_);
v___x_3991_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10);
v___x_3992_ = lean_float_div(v___x_3990_, v___x_3991_);
v___x_3993_ = lean_float_of_nat(v___x_3989_);
v___x_3994_ = lean_float_div(v___x_3993_, v___x_3991_);
v___x_3995_ = lean_box_float(v___x_3992_);
v___x_3996_ = lean_box_float(v___x_3994_);
v___x_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3998_, 0, v_a_3988_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3981_, v_hasTrace_3971_, v___x_3982_, v_options_3969_, v___x_3984_, v___y_3986_, v___f_3980_, v___x_3998_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
v___y_3945_ = v___x_3999_;
goto v___jp_3944_;
}
v___jp_4000_:
{
lean_object* v___x_4004_; double v___x_4005_; double v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4004_ = lean_io_get_num_heartbeats();
v___x_4005_ = lean_float_of_nat(v___y_4002_);
v___x_4006_ = lean_float_of_nat(v___x_4004_);
v___x_4007_ = lean_box_float(v___x_4005_);
v___x_4008_ = lean_box_float(v___x_4006_);
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4010_, 0, v_a_4003_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
v___x_4011_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3981_, v_hasTrace_3971_, v___x_3982_, v_options_3969_, v___x_3984_, v___y_4001_, v___f_3980_, v___x_4010_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
v___y_3945_ = v___x_4011_;
goto v___jp_3944_;
}
v___jp_4012_:
{
lean_object* v___x_4013_; 
v___x_4013_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3913_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; uint8_t v___x_4016_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4013_, 1);
v___x_4015_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4016_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3969_, v___x_4015_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = lean_io_mono_nanos_now();
lean_inc_ref(v_e_3900_);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3973_, v_e_3900_, v_snd_3925_, v_proc_3929_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v_snd_3925_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set_tag(v___x_4021_, 1);
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
v___y_3986_ = v_a_4014_;
v___y_3987_ = v___x_4017_;
v_a_3988_ = v___x_4024_;
goto v___jp_3985_;
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
v_a_4027_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4018_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4018_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set_tag(v___x_4029_, 0);
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
v___y_3986_ = v_a_4014_;
v___y_3987_ = v___x_4017_;
v_a_3988_ = v___x_4032_;
goto v___jp_3985_;
}
}
}
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_e_3900_);
v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3973_, v_e_3900_, v_snd_3925_, v_proc_3929_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v_snd_3925_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set_tag(v___x_4039_, 1);
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
v___y_4001_ = v_a_4014_;
v___y_4002_ = v___x_4035_;
v_a_4003_ = v___x_4042_;
goto v___jp_4000_;
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_a_4045_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4036_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4036_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set_tag(v___x_4047_, 0);
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
v___y_4001_ = v_a_4014_;
v___y_4002_ = v___x_4035_;
v_a_4003_ = v___x_4050_;
goto v___jp_4000_;
}
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v___f_3980_);
lean_del_object(v___x_3931_);
lean_dec_ref(v_proc_3929_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec_ref(v_e_3900_);
v_a_4053_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4013_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4013_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_3933_);
lean_del_object(v___x_3931_);
lean_dec_ref(v_proc_3929_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_3916_ = v___x_3942_;
goto v___jp_3915_;
}
v___jp_3935_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___y_3936_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v___x_3934_);
lean_ctor_set(v___x_3927_, 0, v___x_3937_);
v___x_3939_ = v___x_3927_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v___x_3934_);
v___x_3939_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
}
v___jp_3944_:
{
if (lean_obj_tag(v___y_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3959_; 
v_a_3946_ = lean_ctor_get(v___y_3945_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___y_3945_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3948_ = v___y_3945_;
v_isShared_3949_ = v_isSharedCheck_3959_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___y_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3959_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
if (lean_obj_tag(v_a_3946_) == 1)
{
lean_del_object(v___x_3948_);
lean_del_object(v___x_3931_);
lean_dec_ref(v_e_3900_);
v___y_3936_ = v_a_3946_;
goto v___jp_3935_;
}
else
{
if (v___x_3943_ == 0)
{
lean_del_object(v___x_3927_);
if (lean_obj_tag(v_a_3946_) == 0)
{
uint8_t v_done_3950_; 
v_done_3950_ = lean_ctor_get_uint8(v_a_3946_, 0);
if (v_done_3950_ == 1)
{
uint8_t v_contextDependent_3951_; 
v_contextDependent_3951_ = lean_ctor_get_uint8(v_a_3946_, 1);
if (v_contextDependent_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
lean_dec_ref(v_e_3900_);
v___x_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_a_3946_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 1, v___x_3934_);
lean_ctor_set(v___x_3931_, 0, v___x_3952_);
v___x_3954_ = v___x_3931_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3934_);
v___x_3954_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3956_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3954_);
v___x_3956_ = v___x_3948_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
else
{
lean_dec_ref_known(v_a_3946_, 0);
lean_del_object(v___x_3948_);
lean_del_object(v___x_3931_);
v_a_3916_ = v___x_3942_;
goto v___jp_3915_;
}
}
else
{
lean_dec_ref_known(v_a_3946_, 0);
lean_del_object(v___x_3948_);
lean_del_object(v___x_3931_);
v_a_3916_ = v___x_3942_;
goto v___jp_3915_;
}
}
else
{
lean_del_object(v___x_3948_);
lean_dec(v_a_3946_);
lean_del_object(v___x_3931_);
v_a_3916_ = v___x_3942_;
goto v___jp_3915_;
}
}
else
{
lean_del_object(v___x_3948_);
lean_del_object(v___x_3931_);
lean_dec_ref(v_e_3900_);
v___y_3936_ = v_a_3946_;
goto v___jp_3935_;
}
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_del_object(v___x_3931_);
lean_del_object(v___x_3927_);
lean_dec_ref(v_e_3900_);
v_a_3960_ = lean_ctor_get(v___y_3945_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___y_3945_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___y_3945_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___y_3945_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
}
}
v___jp_3915_:
{
size_t v___x_3917_; size_t v___x_3918_; 
v___x_3917_ = ((size_t)1ULL);
v___x_3918_ = lean_usize_add(v_i_3903_, v___x_3917_);
lean_inc_ref(v_a_3916_);
v_i_3903_ = v___x_3918_;
v_b_3904_ = v_a_3916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object* v_erased_4068_, lean_object* v_e_4069_, lean_object* v_as_4070_, lean_object* v_sz_4071_, lean_object* v_i_4072_, lean_object* v_b_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
size_t v_sz_boxed_4084_; size_t v_i_boxed_4085_; lean_object* v_res_4086_; 
v_sz_boxed_4084_ = lean_unbox_usize(v_sz_4071_);
lean_dec(v_sz_4071_);
v_i_boxed_4085_ = lean_unbox_usize(v_i_4072_);
lean_dec(v_i_4072_);
v_res_4086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_4068_, v_e_4069_, v_as_4070_, v_sz_boxed_4084_, v_i_boxed_4085_, v_b_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v_as_4070_);
lean_dec_ref(v_erased_4068_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object* v_tree_4089_, lean_object* v_erased_4090_, lean_object* v_e_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v___x_4102_; lean_object* v_mctx_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4102_ = lean_st_ref_get(v_a_4098_);
v_mctx_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc_ref(v_mctx_4103_);
lean_dec(v___x_4102_);
v___x_4104_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_4103_, v_tree_4089_, v_e_4091_);
lean_dec_ref(v_mctx_4103_);
v___x_4105_ = lean_array_get_size(v___x_4104_);
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = lean_nat_dec_eq(v___x_4105_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; size_t v_sz_4109_; size_t v___x_4110_; lean_object* v___x_4111_; 
v___x_4108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v_sz_4109_ = lean_array_size(v___x_4104_);
v___x_4110_ = ((size_t)0ULL);
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_4090_, v_e_4091_, v___x_4104_, v_sz_4109_, v___x_4110_, v___x_4108_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
lean_dec_ref(v___x_4104_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4125_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4125_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4111_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4125_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v_fst_4116_; 
v_fst_4116_ = lean_ctor_get(v_a_4112_, 0);
lean_inc(v_fst_4116_);
lean_dec(v_a_4112_);
if (lean_obj_tag(v_fst_4116_) == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4117_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4117_, 0, v___x_4107_);
lean_ctor_set_uint8(v___x_4117_, 1, v___x_4107_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v___x_4117_);
v___x_4119_ = v___x_4114_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
else
{
lean_object* v_val_4121_; lean_object* v___x_4123_; 
v_val_4121_ = lean_ctor_get(v_fst_4116_, 0);
lean_inc(v_val_4121_);
lean_dec_ref_known(v_fst_4116_, 1);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v_val_4121_);
v___x_4123_ = v___x_4114_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_val_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
v_a_4126_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4111_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4111_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v___x_4104_);
lean_dec_ref(v_e_4091_);
v___x_4134_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0));
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object* v_tree_4136_, lean_object* v_erased_4137_, lean_object* v_e_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_4136_, v_erased_4137_, v_e_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec_ref(v_erased_4137_);
lean_dec_ref(v_tree_4136_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object* v_00_u03b1_4150_, lean_object* v_x_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_4151_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4163_, lean_object* v_x_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(v_00_u03b1_4163_, v_x_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object* v_oldTraces_4176_, lean_object* v_data_4177_, lean_object* v_ref_4178_, lean_object* v_msg_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_4176_, v_data_4177_, v_ref_4178_, v_msg_4179_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object* v_oldTraces_4191_, lean_object* v_data_4192_, lean_object* v_ref_4193_, lean_object* v_msg_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_oldTraces_4191_, v_data_4192_, v_ref_4193_, v_msg_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
return v_res_4205_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default();
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase();
l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase = _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs);
l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef);
lean_dec_ref(res);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
}
#ifdef __cplusplus
}
#endif
