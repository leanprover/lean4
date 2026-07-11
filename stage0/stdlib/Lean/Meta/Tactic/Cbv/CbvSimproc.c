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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_initializing();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(lean_object* v_pre_28_){
_start:
{
lean_inc(v_pre_28_);
return v_pre_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(lean_object* v_pre_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(v_pre_29_);
lean_dec(v_pre_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_pre_34_){
_start:
{
lean_inc(v_pre_34_);
return v_pre_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_pre_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_pre_38_);
lean_dec(v_pre_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(lean_object* v_eval_41_){
_start:
{
lean_inc(v_eval_41_);
return v_eval_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(lean_object* v_eval_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(v_eval_42_);
lean_dec(v_eval_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_eval_47_){
_start:
{
lean_inc(v_eval_47_);
return v_eval_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_eval_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_eval_51_);
lean_dec(v_eval_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(lean_object* v_post_54_){
_start:
{
lean_inc(v_post_54_);
return v_post_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(lean_object* v_post_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(v_post_55_);
lean_dec(v_post_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_post_60_){
_start:
{
lean_inc(v_post_60_);
return v_post_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_post_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_post_64_);
lean_dec(v_post_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(uint8_t v_x_69_, uint8_t v_y_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_69_);
v___x_72_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_y_70_);
v___x_73_ = lean_nat_dec_eq(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_17__boxed_76_; uint8_t v_y_18__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_17__boxed_76_ = lean_unbox(v_x_74_);
v_y_18__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(v_x_17__boxed_76_, v_y_18__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(uint8_t v_x_82_){
_start:
{
switch(v_x_82_)
{
case 0:
{
uint64_t v___x_83_; 
v___x_83_ = 0ULL;
return v___x_83_;
}
case 1:
{
uint64_t v___x_84_; 
v___x_84_ = 1ULL;
return v___x_84_;
}
default: 
{
uint64_t v___x_85_; 
v___x_85_ = 2ULL;
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(lean_object* v_x_86_){
_start:
{
uint8_t v_x_40__boxed_87_; uint64_t v_res_88_; lean_object* v_r_89_; 
v_x_40__boxed_87_ = lean_unbox(v_x_86_);
v_res_88_ = l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(v_x_40__boxed_87_);
v_r_89_ = lean_box_uint64(v_res_88_);
return v_r_89_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_to_int(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_to_int(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(uint8_t v_x_105_, lean_object* v_prec_106_){
_start:
{
lean_object* v___y_108_; lean_object* v___y_115_; lean_object* v___y_122_; 
switch(v_x_105_)
{
case 0:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1024u);
v___x_129_ = lean_nat_dec_le(v___x_128_, v_prec_106_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_108_ = v___x_130_;
goto v___jp_107_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_108_ = v___x_131_;
goto v___jp_107_;
}
}
case 1:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = lean_nat_dec_le(v___x_132_, v_prec_106_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_115_ = v___x_134_;
goto v___jp_114_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_115_ = v___x_135_;
goto v___jp_114_;
}
}
default: 
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1024u);
v___x_137_ = lean_nat_dec_le(v___x_136_, v_prec_106_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_122_ = v___x_138_;
goto v___jp_121_;
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_122_ = v___x_139_;
goto v___jp_121_;
}
}
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1));
lean_inc(v___y_108_);
v___x_110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_prec_106_);
return v___x_113_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_116_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3));
lean_inc(v___y_115_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___y_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = l_Repr_addAppParen(v___x_119_, v_prec_106_);
return v___x_120_;
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5));
lean_inc(v___y_122_);
v___x_124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_124_, 0, v___y_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = 0;
v___x_126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_125_);
v___x_127_ = l_Repr_addAppParen(v___x_126_, v_prec_106_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(lean_object* v_x_140_, lean_object* v_prec_141_){
_start:
{
uint8_t v_x_177__boxed_142_; lean_object* v_res_143_; 
v_x_177__boxed_142_ = lean_unbox(v_x_140_);
v_res_143_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(v_x_177__boxed_142_, v_prec_141_);
lean_dec(v_prec_141_);
return v_res_143_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6));
v___x_161_ = l_Lean_mkConst(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9));
v___x_172_ = l_Lean_mkConst(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_box(0);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12));
v___x_183_ = l_Lean_mkConst(v___x_182_, v___x_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(uint8_t v_x_184_){
_start:
{
switch(v_x_184_)
{
case 0:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
return v___x_185_;
}
case 1:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
return v___x_186_;
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(lean_object* v_x_188_){
_start:
{
uint8_t v_x_196__boxed_189_; lean_object* v_res_190_; 
v_x_196__boxed_189_ = lean_unbox(v_x_188_);
v_res_190_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(v_x_196__boxed_189_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_box(0);
v___x_199_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1));
v___x_200_ = l_Lean_mkConst(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3(void){
_start:
{
lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2);
v___f_202_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0));
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___f_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3);
return v___x_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(lean_object* v_e_u2081_213_, lean_object* v_e_u2082_214_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_215_; lean_object* v_toCbvSimprocOLeanEntry_216_; lean_object* v_declName_217_; lean_object* v_declName_218_; uint8_t v___x_219_; 
v_toCbvSimprocOLeanEntry_215_ = lean_ctor_get(v_e_u2081_213_, 0);
v_toCbvSimprocOLeanEntry_216_ = lean_ctor_get(v_e_u2082_214_, 0);
v_declName_217_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_215_, 0);
v_declName_218_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_216_, 0);
v___x_219_ = lean_name_eq(v_declName_217_, v_declName_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(lean_object* v_e_u2081_220_, lean_object* v_e_u2082_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(v_e_u2081_220_, v_e_u2082_221_);
lean_dec_ref(v_e_u2082_221_);
lean_dec_ref(v_e_u2081_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(lean_object* v_e_226_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_227_; lean_object* v_declName_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_toCbvSimprocOLeanEntry_227_ = lean_ctor_get(v_e_226_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_227_);
lean_dec_ref(v_e_226_);
v_declName_228_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_227_, 0);
lean_inc(v_declName_228_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_227_);
v___x_229_ = 1;
v___x_230_ = l_Lean_Name_toString(v_declName_228_, v___x_229_);
v___x_231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_234_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object* v_00_u03b2_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_box(0));
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2);
v___x_244_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1);
v___x_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
lean_ctor_set(v___x_245_, 3, v___x_243_);
lean_ctor_set(v___x_245_, 4, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(lean_object* v_xs_248_, lean_object* v_v_249_, lean_object* v_i_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_array_get_size(v_xs_248_);
v___x_252_ = lean_nat_dec_lt(v_i_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_i_250_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_array_fget_borrowed(v_xs_248_, v_i_250_);
v___x_255_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_254_, v_v_249_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_i_250_, v___x_256_);
lean_dec(v_i_250_);
v_i_250_ = v___x_257_;
goto _start;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_i_250_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17___boxed(lean_object* v_xs_260_, lean_object* v_v_261_, lean_object* v_i_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(v_xs_260_, v_v_261_, v_i_262_);
lean_dec(v_v_261_);
lean_dec_ref(v_xs_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(lean_object* v_xs_264_, lean_object* v_v_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11_spec__17(v_xs_264_, v_v_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11___boxed(lean_object* v_xs_268_, lean_object* v_v_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(v_xs_268_, v_v_269_);
lean_dec(v_v_269_);
lean_dec_ref(v_xs_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(lean_object* v_x_271_, lean_object* v_keys_272_, lean_object* v_v_273_, lean_object* v_k_274_, lean_object* v_x_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_c_278_; lean_object* v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_x_271_, v___x_276_);
v_c_278_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_272_, v_v_273_, v___x_277_);
lean_dec(v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_k_274_);
lean_ctor_set(v___x_279_, 1, v_c_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_x_280_, lean_object* v_keys_281_, lean_object* v_v_282_, lean_object* v_k_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_280_, v_keys_281_, v_v_282_, v_k_283_, v_x_284_);
lean_dec_ref(v_keys_281_);
lean_dec(v_x_280_);
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
lean_object* v_fst_288_; lean_object* v_fst_289_; uint8_t v___x_290_; 
v_fst_288_ = lean_ctor_get(v_a_286_, 0);
v_fst_289_ = lean_ctor_get(v_b_287_, 0);
v___x_290_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_288_, v_fst_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1___boxed(lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_a_291_, v_b_292_);
lean_dec_ref(v_b_292_);
lean_dec_ref(v_a_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object* v_vs_295_, lean_object* v_v_296_, lean_object* v_i_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_array_get_size(v_vs_295_);
v___x_299_ = lean_nat_dec_lt(v_i_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v_i_297_);
v___x_300_ = lean_array_push(v_vs_295_, v_v_296_);
return v___x_300_;
}
else
{
lean_object* v_toCbvSimprocOLeanEntry_301_; lean_object* v_declName_302_; lean_object* v___x_303_; lean_object* v_toCbvSimprocOLeanEntry_304_; lean_object* v_declName_305_; uint8_t v___x_306_; 
v_toCbvSimprocOLeanEntry_301_ = lean_ctor_get(v_v_296_, 0);
v_declName_302_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_301_, 0);
v___x_303_ = lean_array_fget_borrowed(v_vs_295_, v_i_297_);
v_toCbvSimprocOLeanEntry_304_ = lean_ctor_get(v___x_303_, 0);
v_declName_305_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_304_, 0);
v___x_306_ = lean_name_eq(v_declName_302_, v_declName_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_297_, v___x_307_);
lean_dec(v_i_297_);
v_i_297_ = v___x_308_;
goto _start;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_array_fset(v_vs_295_, v_i_297_, v_v_296_);
lean_dec(v_i_297_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object* v_vs_311_, lean_object* v_v_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(v_vs_311_, v_v_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(lean_object* v_x_319_, lean_object* v_keys_320_, lean_object* v_v_321_, lean_object* v_k_322_, lean_object* v_as_323_, lean_object* v_k_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_mid_329_; lean_object* v_midVal_330_; uint8_t v___x_331_; 
v___x_327_ = lean_nat_add(v_x_325_, v_x_326_);
v___x_328_ = lean_unsigned_to_nat(1u);
v_mid_329_ = lean_nat_shiftr(v___x_327_, v___x_328_);
lean_dec(v___x_327_);
v_midVal_330_ = lean_array_fget(v_as_323_, v_mid_329_);
v___x_331_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_midVal_330_, v_k_324_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; 
lean_dec(v_x_326_);
v___x_332_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_324_, v_midVal_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
lean_dec(v_x_325_);
v___x_333_ = lean_array_get_size(v_as_323_);
v___x_334_ = lean_nat_dec_lt(v_mid_329_, v___x_333_);
if (v___x_334_ == 0)
{
lean_dec(v_midVal_330_);
lean_dec(v_mid_329_);
lean_dec(v_k_322_);
lean_dec_ref(v_v_321_);
return v_as_323_;
}
else
{
lean_object* v_snd_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_347_; 
v_snd_335_ = lean_ctor_get(v_midVal_330_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_midVal_330_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_midVal_330_, 0);
lean_dec(v_unused_348_);
v___x_337_ = v_midVal_330_;
v_isShared_338_ = v_isSharedCheck_347_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_snd_335_);
lean_dec(v_midVal_330_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_347_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v_xs_x27_340_; lean_object* v___x_341_; lean_object* v_c_342_; lean_object* v___x_344_; 
v___x_339_ = lean_box(0);
v_xs_x27_340_ = lean_array_fset(v_as_323_, v_mid_329_, v___x_339_);
v___x_341_ = lean_nat_add(v_x_319_, v___x_328_);
v_c_342_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_320_, v_v_321_, v___x_341_, v_snd_335_);
lean_dec(v___x_341_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_c_342_);
lean_ctor_set(v___x_337_, 0, v_k_322_);
v___x_344_ = v___x_337_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_k_322_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_c_342_);
v___x_344_ = v_reuseFailAlloc_346_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_fset(v_xs_x27_340_, v_mid_329_, v___x_344_);
lean_dec(v_mid_329_);
return v___x_345_;
}
}
}
}
else
{
lean_dec(v_midVal_330_);
v_x_326_ = v_mid_329_;
goto _start;
}
}
else
{
uint8_t v___x_350_; 
lean_dec(v_midVal_330_);
v___x_350_ = lean_nat_dec_eq(v_mid_329_, v_x_325_);
if (v___x_350_ == 0)
{
lean_dec(v_x_325_);
v_x_325_ = v_mid_329_;
goto _start;
}
else
{
lean_object* v___x_352_; lean_object* v_c_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_j_356_; lean_object* v_as_357_; lean_object* v___x_358_; 
lean_dec(v_mid_329_);
lean_dec(v_x_326_);
v___x_352_ = lean_nat_add(v_x_319_, v___x_328_);
v_c_353_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_320_, v_v_321_, v___x_352_);
lean_dec(v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_k_322_);
lean_ctor_set(v___x_354_, 1, v_c_353_);
v___x_355_ = lean_nat_add(v_x_325_, v___x_328_);
lean_dec(v_x_325_);
v_j_356_ = lean_array_get_size(v_as_323_);
v_as_357_ = lean_array_push(v_as_323_, v___x_354_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_355_, v_as_357_, v_j_356_);
lean_dec(v___x_355_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(lean_object* v_x_359_, lean_object* v_keys_360_, lean_object* v_v_361_, lean_object* v_k_362_, lean_object* v_as_363_, lean_object* v_k_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_array_get_size(v_as_363_);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_fget_borrowed(v_as_363_, v___x_366_);
v___x_369_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_364_, v___x_368_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v___x_368_, v_k_364_);
v___x_371_ = lean_bool_not(v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_sub(v___x_365_, v___x_372_);
v___x_374_ = lean_array_fget_borrowed(v_as_363_, v___x_373_);
v___x_375_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v___x_374_, v_k_364_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_364_, v___x_374_);
v___x_377_ = lean_bool_not(v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v_as_363_, v_k_364_, v___x_366_, v___x_373_);
return v___x_378_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = lean_nat_dec_lt(v___x_373_, v___x_365_);
if (v___x_379_ == 0)
{
lean_dec(v___x_373_);
lean_dec(v_k_362_);
lean_dec_ref(v_v_361_);
return v_as_363_;
}
else
{
lean_object* v___x_380_; lean_object* v_xs_x27_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc(v___x_374_);
v___x_380_ = lean_box(0);
v_xs_x27_381_ = lean_array_fset(v_as_363_, v___x_373_, v___x_380_);
v___x_382_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_374_);
v___x_383_ = lean_array_fset(v_xs_x27_381_, v___x_373_, v___x_382_);
lean_dec(v___x_373_);
return v___x_383_;
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v___x_385_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_384_);
v___x_386_ = lean_array_push(v_as_363_, v___x_385_);
return v___x_386_;
}
}
else
{
uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_lt(v___x_366_, v___x_365_);
if (v___x_387_ == 0)
{
lean_dec(v_k_362_);
lean_dec_ref(v_v_361_);
return v_as_363_;
}
else
{
lean_object* v___x_388_; lean_object* v_xs_x27_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc(v___x_368_);
v___x_388_ = lean_box(0);
v_xs_x27_389_ = lean_array_fset(v_as_363_, v___x_366_, v___x_388_);
v___x_390_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_368_);
v___x_391_ = lean_array_fset(v_xs_x27_389_, v___x_366_, v___x_390_);
return v___x_391_;
}
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_as_394_; lean_object* v___x_395_; 
v___x_392_ = lean_box(0);
v___x_393_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_392_);
v_as_394_ = lean_array_push(v_as_363_, v___x_393_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_366_, v_as_394_, v___x_365_);
return v___x_395_;
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_box(0);
v___x_397_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_396_);
v___x_398_ = lean_array_push(v_as_363_, v___x_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object* v_keys_399_, lean_object* v_v_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_vs_403_; lean_object* v_children_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_421_; 
v_vs_403_ = lean_ctor_get(v_x_402_, 0);
v_children_404_ = lean_ctor_get(v_x_402_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_421_ == 0)
{
v___x_406_ = v_x_402_;
v_isShared_407_ = v_isSharedCheck_421_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_children_404_);
lean_inc(v_vs_403_);
lean_dec(v_x_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_421_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_keys_399_);
v___x_409_ = lean_nat_dec_lt(v_x_401_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v_vs_403_, v_v_400_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_410_);
v___x_412_ = v___x_406_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_children_404_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
else
{
lean_object* v_k_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_c_417_; lean_object* v___x_419_; 
v_k_414_ = lean_array_fget_borrowed(v_keys_399_, v_x_401_);
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1));
lean_inc_n(v_k_414_, 2);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_k_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v_c_417_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_x_401_, v_keys_399_, v_v_400_, v_k_414_, v_children_404_, v___x_416_);
lean_dec_ref_known(v___x_416_, 2);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_c_417_);
v___x_419_ = v___x_406_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_vs_403_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_c_417_);
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
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(lean_object* v_x_422_, lean_object* v_keys_423_, lean_object* v_v_424_, lean_object* v_k_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
v_snd_427_ = lean_ctor_get(v_x_426_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v_x_426_, 0);
lean_dec(v_unused_438_);
v___x_429_ = v_x_426_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_dec(v_x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_c_433_; lean_object* v___x_435_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_add(v_x_422_, v___x_431_);
v_c_433_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_423_, v_v_424_, v___x_432_, v_snd_427_);
lean_dec(v___x_432_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_c_433_);
lean_ctor_set(v___x_429_, 0, v_k_425_);
v___x_435_ = v___x_429_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_k_425_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_c_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2___boxed(lean_object* v_x_439_, lean_object* v_keys_440_, lean_object* v_v_441_, lean_object* v_k_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_439_, v_keys_440_, v_v_441_, v_k_442_, v_x_443_);
lean_dec_ref(v_keys_440_);
lean_dec(v_x_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object* v_keys_445_, lean_object* v_v_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_445_, v_v_446_, v_x_447_, v_x_448_);
lean_dec(v_x_447_);
lean_dec_ref(v_keys_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object* v_x_450_, lean_object* v_keys_451_, lean_object* v_v_452_, lean_object* v_k_453_, lean_object* v_as_454_, lean_object* v_k_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_450_, v_keys_451_, v_v_452_, v_k_453_, v_as_454_, v_k_455_, v_x_456_, v_x_457_);
lean_dec_ref(v_k_455_);
lean_dec_ref(v_keys_451_);
lean_dec(v_x_450_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___boxed(lean_object* v_x_459_, lean_object* v_keys_460_, lean_object* v_v_461_, lean_object* v_k_462_, lean_object* v_as_463_, lean_object* v_k_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_x_459_, v_keys_460_, v_v_461_, v_k_462_, v_as_463_, v_k_464_);
lean_dec_ref(v_k_464_);
lean_dec_ref(v_keys_460_);
lean_dec(v_x_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(lean_object* v_keys_466_, lean_object* v_v_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_466_, v_v_467_, v___x_469_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_val_472_ = lean_ctor_get(v_x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v_x_468_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v_x_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_466_, v_v_467_, v___x_476_, v_val_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0___boxed(lean_object* v_keys_482_, lean_object* v_v_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_482_, v_v_483_, v_x_484_);
lean_dec_ref(v_keys_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_ks_490_; lean_object* v_vs_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_515_; 
v_ks_490_ = lean_ctor_get(v_x_486_, 0);
v_vs_491_ = lean_ctor_get(v_x_486_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_515_ == 0)
{
v___x_493_ = v_x_486_;
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_vs_491_);
lean_inc(v_ks_490_);
lean_dec(v_x_486_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_array_get_size(v_ks_490_);
v___x_496_ = lean_nat_dec_lt(v_x_487_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v_x_487_);
v___x_497_ = lean_array_push(v_ks_490_, v_x_488_);
v___x_498_ = lean_array_push(v_vs_491_, v_x_489_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_498_);
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_500_ = v___x_493_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
else
{
lean_object* v_k_x27_502_; uint8_t v___x_503_; 
v_k_x27_502_ = lean_array_fget_borrowed(v_ks_490_, v_x_487_);
v___x_503_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_488_, v_k_x27_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; 
if (v_isShared_494_ == 0)
{
v___x_505_ = v___x_493_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_ks_490_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_vs_491_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_x_487_, v___x_506_);
lean_dec(v_x_487_);
v_x_486_ = v___x_505_;
v_x_487_ = v___x_507_;
goto _start;
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_array_fset(v_ks_490_, v_x_487_, v_x_488_);
v___x_511_ = lean_array_fset(v_vs_491_, v_x_487_, v_x_489_);
lean_dec(v_x_487_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_511_);
lean_ctor_set(v___x_493_, 0, v___x_510_);
v___x_513_ = v___x_493_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(lean_object* v_n_516_, lean_object* v_k_517_, lean_object* v_v_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(v_n_516_, v___x_519_, v_k_517_, v_v_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(lean_object* v_x_522_, size_t v_x_523_, size_t v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v_es_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v_j_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_es_527_ = lean_ctor_get(v_x_522_, 0);
v___x_528_ = ((size_t)31ULL);
v___x_529_ = lean_usize_land(v_x_523_, v___x_528_);
v_j_530_ = lean_usize_to_nat(v___x_529_);
v___x_531_ = lean_array_get_size(v_es_527_);
v___x_532_ = lean_nat_dec_lt(v_j_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec(v_j_530_);
lean_dec(v_x_526_);
lean_dec(v_x_525_);
return v_x_522_;
}
else
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_571_; 
lean_inc_ref(v_es_527_);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v_x_522_, 0);
lean_dec(v_unused_572_);
v___x_534_ = v_x_522_;
v_isShared_535_ = v_isSharedCheck_571_;
goto v_resetjp_533_;
}
else
{
lean_dec(v_x_522_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_571_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_v_536_; lean_object* v___x_537_; lean_object* v_xs_x27_538_; lean_object* v___y_540_; 
v_v_536_ = lean_array_fget(v_es_527_, v_j_530_);
v___x_537_ = lean_box(0);
v_xs_x27_538_ = lean_array_fset(v_es_527_, v_j_530_, v___x_537_);
switch(lean_obj_tag(v_v_536_))
{
case 0:
{
lean_object* v_key_545_; lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_556_; 
v_key_545_ = lean_ctor_get(v_v_536_, 0);
v_val_546_ = lean_ctor_get(v_v_536_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_v_536_);
if (v_isSharedCheck_556_ == 0)
{
v___x_548_ = v_v_536_;
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_inc(v_key_545_);
lean_dec(v_v_536_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v___x_550_; 
v___x_550_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_525_, v_key_545_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_del_object(v___x_548_);
v___x_551_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_545_, v_val_546_, v_x_525_, v_x_526_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
v___y_540_ = v___x_552_;
goto v___jp_539_;
}
else
{
lean_object* v___x_554_; 
lean_dec(v_val_546_);
lean_dec(v_key_545_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_x_526_);
lean_ctor_set(v___x_548_, 0, v_x_525_);
v___x_554_ = v___x_548_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_x_525_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_x_526_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v___y_540_ = v___x_554_;
goto v___jp_539_;
}
}
}
}
case 1:
{
lean_object* v_node_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_569_; 
v_node_557_ = lean_ctor_get(v_v_536_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_v_536_);
if (v_isSharedCheck_569_ == 0)
{
v___x_559_ = v_v_536_;
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_node_557_);
lean_dec(v_v_536_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_usize_shift_right(v_x_523_, v___x_561_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_x_524_, v___x_563_);
v___x_565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_node_557_, v___x_562_, v___x_564_, v_x_525_, v_x_526_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_565_);
v___x_567_ = v___x_559_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_540_ = v___x_567_;
goto v___jp_539_;
}
}
}
default: 
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_x_525_);
lean_ctor_set(v___x_570_, 1, v_x_526_);
v___y_540_ = v___x_570_;
goto v___jp_539_;
}
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_array_fset(v_xs_x27_538_, v_j_530_, v___y_540_);
lean_dec(v_j_530_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_541_);
v___x_543_ = v___x_534_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
else
{
lean_object* v_ks_573_; lean_object* v_vs_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_594_; 
v_ks_573_ = lean_ctor_get(v_x_522_, 0);
v_vs_574_ = lean_ctor_get(v_x_522_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_594_ == 0)
{
v___x_576_ = v_x_522_;
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_vs_574_);
lean_inc(v_ks_573_);
lean_dec(v_x_522_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_594_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_ks_573_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_vs_574_);
v___x_579_ = v_reuseFailAlloc_593_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v_newNode_580_; uint8_t v___y_582_; size_t v___x_588_; uint8_t v___x_589_; 
v_newNode_580_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(v___x_579_, v_x_525_, v_x_526_);
v___x_588_ = ((size_t)7ULL);
v___x_589_ = lean_usize_dec_le(v___x_588_, v_x_524_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_580_);
v___x_591_ = lean_unsigned_to_nat(4u);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
v___y_582_ = v___x_592_;
goto v___jp_581_;
}
else
{
v___y_582_ = v___x_589_;
goto v___jp_581_;
}
v___jp_581_:
{
if (v___y_582_ == 0)
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_ks_583_ = lean_ctor_get(v_newNode_580_, 0);
lean_inc_ref(v_ks_583_);
v_vs_584_ = lean_ctor_get(v_newNode_580_, 1);
lean_inc_ref(v_vs_584_);
lean_dec_ref(v_newNode_580_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0);
v___x_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_x_524_, v_ks_583_, v_vs_584_, v___x_585_, v___x_586_);
lean_dec_ref(v_vs_584_);
lean_dec_ref(v_ks_583_);
return v___x_587_;
}
else
{
return v_newNode_580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(size_t v_depth_595_, lean_object* v_keys_596_, lean_object* v_vals_597_, lean_object* v_i_598_, lean_object* v_entries_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_keys_596_);
v___x_601_ = lean_nat_dec_lt(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_i_598_);
return v_entries_599_;
}
else
{
lean_object* v_k_602_; lean_object* v_v_603_; uint64_t v___x_604_; size_t v_h_605_; size_t v___x_606_; lean_object* v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v_h_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_k_602_ = lean_array_fget_borrowed(v_keys_596_, v_i_598_);
v_v_603_ = lean_array_fget_borrowed(v_vals_597_, v_i_598_);
v___x_604_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_602_);
v_h_605_ = lean_uint64_to_usize(v___x_604_);
v___x_606_ = ((size_t)5ULL);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_sub(v_depth_595_, v___x_608_);
v___x_610_ = lean_usize_mul(v___x_606_, v___x_609_);
v_h_611_ = lean_usize_shift_right(v_h_605_, v___x_610_);
v___x_612_ = lean_nat_add(v_i_598_, v___x_607_);
lean_dec(v_i_598_);
lean_inc(v_v_603_);
lean_inc(v_k_602_);
v___x_613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_entries_599_, v_h_611_, v_depth_595_, v_k_602_, v_v_603_);
v_i_598_ = v___x_612_;
v_entries_599_ = v___x_613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg___boxed(lean_object* v_depth_615_, lean_object* v_keys_616_, lean_object* v_vals_617_, lean_object* v_i_618_, lean_object* v_entries_619_){
_start:
{
size_t v_depth_boxed_620_; lean_object* v_res_621_; 
v_depth_boxed_620_ = lean_unbox_usize(v_depth_615_);
lean_dec(v_depth_615_);
v_res_621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_depth_boxed_620_, v_keys_616_, v_vals_617_, v_i_618_, v_entries_619_);
lean_dec_ref(v_vals_617_);
lean_dec_ref(v_keys_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
size_t v_x_2415__boxed_627_; size_t v_x_2416__boxed_628_; lean_object* v_res_629_; 
v_x_2415__boxed_627_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_x_2416__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_x_622_, v_x_2415__boxed_627_, v_x_2416__boxed_628_, v_x_625_, v_x_626_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object* v_keys_630_, lean_object* v_v_631_, lean_object* v_x_632_, size_t v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v_es_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v_j_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_es_636_ = lean_ctor_get(v_x_632_, 0);
v___x_637_ = ((size_t)31ULL);
v___x_638_ = lean_usize_land(v_x_633_, v___x_637_);
v_j_639_ = lean_usize_to_nat(v___x_638_);
v___x_640_ = lean_array_get_size(v_es_636_);
v___x_641_ = lean_nat_dec_lt(v_j_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v_j_639_);
lean_dec(v_x_635_);
lean_dec_ref(v_v_631_);
return v_x_632_;
}
else
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_709_; 
lean_inc_ref(v_es_636_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_x_632_, 0);
lean_dec(v_unused_710_);
v___x_643_ = v_x_632_;
v_isShared_644_ = v_isSharedCheck_709_;
goto v_resetjp_642_;
}
else
{
lean_dec(v_x_632_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_709_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_v_645_; lean_object* v___x_646_; lean_object* v_xs_x27_647_; lean_object* v___y_649_; 
v_v_645_ = lean_array_fget(v_es_636_, v_j_639_);
v___x_646_ = lean_box(0);
v_xs_x27_647_ = lean_array_fset(v_es_636_, v_j_639_, v___x_646_);
switch(lean_obj_tag(v_v_645_))
{
case 0:
{
lean_object* v_key_654_; lean_object* v_val_655_; uint8_t v___x_656_; 
v_key_654_ = lean_ctor_get(v_v_645_, 0);
v_val_655_ = lean_ctor_get(v_v_645_, 1);
v___x_656_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_635_, v_key_654_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(0);
v___x_658_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_630_, v_v_631_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec(v_x_635_);
v___y_649_ = v_v_645_;
goto v___jp_648_;
}
else
{
lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
lean_inc(v_val_655_);
lean_inc(v_key_654_);
lean_dec_ref_known(v_v_645_, 2);
v_val_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_654_, v_val_655_, v_x_635_, v_val_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
v___y_649_ = v___x_665_;
goto v___jp_648_;
}
}
}
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_val_655_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_v_645_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_679_ = lean_ctor_get(v_v_645_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_v_645_, 0);
lean_dec(v_unused_680_);
v___x_669_ = v_v_645_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_v_645_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_val_655_);
v___x_672_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_630_, v_v_631_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; 
lean_del_object(v___x_669_);
lean_dec(v_x_635_);
v___x_673_ = lean_box(2);
v___y_649_ = v___x_673_;
goto v___jp_648_;
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; 
v_val_674_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v___x_672_, 1);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v_val_674_);
lean_ctor_set(v___x_669_, 0, v_x_635_);
v___x_676_ = v___x_669_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_x_635_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_val_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v___y_649_ = v___x_676_;
goto v___jp_648_;
}
}
}
}
}
case 1:
{
lean_object* v_node_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_704_; 
v_node_681_ = lean_ctor_get(v_v_645_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_v_645_);
if (v_isSharedCheck_704_ == 0)
{
v___x_683_ = v_v_645_;
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_node_681_);
lean_dec(v_v_645_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v_newNode_689_; lean_object* v___x_690_; 
v___x_685_ = ((size_t)5ULL);
v___x_686_ = lean_usize_shift_right(v_x_633_, v___x_685_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_x_634_, v___x_687_);
v_newNode_689_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_630_, v_v_631_, v_node_681_, v___x_686_, v___x_688_, v_x_635_);
lean_inc_ref(v_newNode_689_);
v___x_690_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_689_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_692_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_newNode_689_);
v___x_692_ = v___x_683_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_newNode_689_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v___y_649_ = v___x_692_;
goto v___jp_648_;
}
}
else
{
lean_object* v_val_694_; lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v_newNode_689_);
lean_del_object(v___x_683_);
v_val_694_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_690_, 1);
v_fst_695_ = lean_ctor_get(v_val_694_, 0);
v_snd_696_ = lean_ctor_get(v_val_694_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_val_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v_val_694_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snd_696_);
lean_inc(v_fst_695_);
lean_dec(v_val_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fst_695_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v___y_649_ = v___x_701_;
goto v___jp_648_;
}
}
}
}
}
default: 
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_630_, v_v_631_, v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec(v_x_635_);
v___y_649_ = v_v_645_;
goto v___jp_648_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_x_635_);
lean_ctor_set(v___x_708_, 1, v_val_707_);
v___y_649_ = v___x_708_;
goto v___jp_648_;
}
}
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_array_fset(v_xs_x27_647_, v_j_639_, v___y_649_);
lean_dec(v_j_639_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_650_);
v___x_652_ = v___x_643_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
else
{
lean_object* v_ks_711_; lean_object* v_vs_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_745_; 
v_ks_711_ = lean_ctor_get(v_x_632_, 0);
v_vs_712_ = lean_ctor_get(v_x_632_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_745_ == 0)
{
v___x_714_ = v_x_632_;
v_isShared_715_ = v_isSharedCheck_745_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_vs_712_);
lean_inc(v_ks_711_);
lean_dec(v_x_632_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_745_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(v_ks_711_, v_x_635_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_718_; 
if (v_isShared_715_ == 0)
{
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_ks_711_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_vs_712_);
v___x_718_ = v_reuseFailAlloc_723_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_box(0);
v___x_720_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_630_, v_v_631_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec(v_x_635_);
return v___x_718_;
}
else
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v___x_718_, v_x_633_, v_x_634_, v_x_635_, v_val_721_);
return v___x_722_;
}
}
}
else
{
lean_object* v_val_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_744_; 
v_val_724_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_744_ == 0)
{
v___x_726_ = v___x_716_;
v_isShared_727_ = v_isSharedCheck_744_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_val_724_);
lean_dec(v___x_716_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_744_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_v_x27_728_; lean_object* v_keys_729_; lean_object* v_vals_730_; lean_object* v___x_732_; 
v_v_x27_728_ = lean_array_fget(v_vs_712_, v_val_724_);
lean_inc(v_val_724_);
v_keys_729_ = l_Array_eraseIdx___redArg(v_ks_711_, v_val_724_);
v_vals_730_ = l_Array_eraseIdx___redArg(v_vs_712_, v_val_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v_v_x27_728_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_v_x27_728_);
v___x_732_ = v_reuseFailAlloc_743_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_630_, v_v_631_, v___x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_735_; 
lean_dec(v_x_635_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_vals_730_);
lean_ctor_set(v___x_714_, 0, v_keys_729_);
v___x_735_ = v___x_714_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_keys_729_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_vals_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v_val_737_; lean_object* v_keys_738_; lean_object* v_vals_739_; lean_object* v___x_741_; 
v_val_737_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_733_, 1);
v_keys_738_ = lean_array_push(v_keys_729_, v_x_635_);
v_vals_739_ = lean_array_push(v_vals_730_, v_val_737_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_vals_739_);
lean_ctor_set(v___x_714_, 0, v_keys_738_);
v___x_741_ = v___x_714_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_keys_738_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_vals_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___boxed(lean_object* v_keys_746_, lean_object* v_v_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
size_t v_x_2571__boxed_752_; size_t v_x_2572__boxed_753_; lean_object* v_res_754_; 
v_x_2571__boxed_752_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_x_2572__boxed_753_ = lean_unbox_usize(v_x_750_);
lean_dec(v_x_750_);
v_res_754_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_746_, v_v_747_, v_x_748_, v_x_2571__boxed_752_, v_x_2572__boxed_753_, v_x_751_);
lean_dec_ref(v_keys_746_);
return v_res_754_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object* v_msg_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0);
v___x_758_ = lean_panic_fn_borrowed(v___x_757_, v_msg_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_762_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2));
v___x_763_ = lean_unsigned_to_nat(23u);
v___x_764_ = lean_unsigned_to_nat(166u);
v___x_765_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1));
v___x_766_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0));
v___x_767_ = l_mkPanicMessageWithDecl(v___x_766_, v___x_765_, v___x_764_, v___x_763_, v___x_762_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object* v_d_768_, lean_object* v_keys_769_, lean_object* v_v_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_array_get_size(v_keys_769_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_nat_dec_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v_k_775_; uint64_t v___x_776_; size_t v_h_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_774_ = lean_box(0);
v_k_775_ = lean_array_get_borrowed(v___x_774_, v_keys_769_, v___x_772_);
v___x_776_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_775_);
v_h_777_ = lean_uint64_to_usize(v___x_776_);
v___x_778_ = ((size_t)1ULL);
lean_inc(v_k_775_);
v___x_779_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_769_, v_v_770_, v_d_768_, v_h_777_, v___x_778_, v_k_775_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_v_770_);
lean_dec_ref(v_d_768_);
v___x_780_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
v___x_781_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v___x_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object* v_d_782_, lean_object* v_keys_783_, lean_object* v_v_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_782_, v_keys_783_, v_v_784_);
lean_dec_ref(v_keys_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v_ks_790_; lean_object* v_vs_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_815_; 
v_ks_790_ = lean_ctor_get(v_x_786_, 0);
v_vs_791_ = lean_ctor_get(v_x_786_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_815_ == 0)
{
v___x_793_ = v_x_786_;
v_isShared_794_ = v_isSharedCheck_815_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_vs_791_);
lean_inc(v_ks_790_);
lean_dec(v_x_786_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_815_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_array_get_size(v_ks_790_);
v___x_796_ = lean_nat_dec_lt(v_x_787_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec(v_x_787_);
v___x_797_ = lean_array_push(v_ks_790_, v_x_788_);
v___x_798_ = lean_array_push(v_vs_791_, v_x_789_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_798_);
lean_ctor_set(v___x_793_, 0, v___x_797_);
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
lean_object* v_k_x27_802_; uint8_t v___x_803_; 
v_k_x27_802_ = lean_array_fget_borrowed(v_ks_790_, v_x_787_);
v___x_803_ = lean_name_eq(v_x_788_, v_k_x27_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; 
if (v_isShared_794_ == 0)
{
v___x_805_ = v___x_793_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_ks_790_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_vs_791_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_x_787_, v___x_806_);
lean_dec(v_x_787_);
v_x_786_ = v___x_805_;
v_x_787_ = v___x_807_;
goto _start;
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = lean_array_fset(v_ks_790_, v_x_787_, v_x_788_);
v___x_811_ = lean_array_fset(v_vs_791_, v_x_787_, v_x_789_);
lean_dec(v_x_787_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_811_);
lean_ctor_set(v___x_793_, 0, v___x_810_);
v___x_813_ = v___x_793_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_816_, lean_object* v_k_817_, lean_object* v_v_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_816_, v___x_819_, v_k_817_, v_v_818_);
return v___x_820_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_821_; uint64_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1723u);
v___x_822_ = lean_uint64_of_nat(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_824_, size_t v_x_825_, size_t v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v_es_829_; size_t v___x_830_; size_t v___x_831_; lean_object* v_j_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_es_829_ = lean_ctor_get(v_x_824_, 0);
v___x_830_ = ((size_t)31ULL);
v___x_831_ = lean_usize_land(v_x_825_, v___x_830_);
v_j_832_ = lean_usize_to_nat(v___x_831_);
v___x_833_ = lean_array_get_size(v_es_829_);
v___x_834_ = lean_nat_dec_lt(v_j_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_dec(v_j_832_);
lean_dec(v_x_828_);
lean_dec(v_x_827_);
return v_x_824_;
}
else
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_873_; 
lean_inc_ref(v_es_829_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_824_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_x_824_, 0);
lean_dec(v_unused_874_);
v___x_836_ = v_x_824_;
v_isShared_837_ = v_isSharedCheck_873_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_x_824_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_873_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_v_838_; lean_object* v___x_839_; lean_object* v_xs_x27_840_; lean_object* v___y_842_; 
v_v_838_ = lean_array_fget(v_es_829_, v_j_832_);
v___x_839_ = lean_box(0);
v_xs_x27_840_ = lean_array_fset(v_es_829_, v_j_832_, v___x_839_);
switch(lean_obj_tag(v_v_838_))
{
case 0:
{
lean_object* v_key_847_; lean_object* v_val_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_key_847_ = lean_ctor_get(v_v_838_, 0);
v_val_848_ = lean_ctor_get(v_v_838_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_v_838_);
if (v_isSharedCheck_858_ == 0)
{
v___x_850_ = v_v_838_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_val_848_);
lean_inc(v_key_847_);
lean_dec(v_v_838_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_name_eq(v_x_827_, v_key_847_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_del_object(v___x_850_);
v___x_853_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_847_, v_val_848_, v_x_827_, v_x_828_);
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___y_842_ = v___x_854_;
goto v___jp_841_;
}
else
{
lean_object* v___x_856_; 
lean_dec(v_val_848_);
lean_dec(v_key_847_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_x_828_);
lean_ctor_set(v___x_850_, 0, v_x_827_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_x_827_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_x_828_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
v___y_842_ = v___x_856_;
goto v___jp_841_;
}
}
}
}
case 1:
{
lean_object* v_node_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_871_; 
v_node_859_ = lean_ctor_get(v_v_838_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_v_838_);
if (v_isSharedCheck_871_ == 0)
{
v___x_861_ = v_v_838_;
v_isShared_862_ = v_isSharedCheck_871_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_node_859_);
lean_dec(v_v_838_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_871_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_863_ = ((size_t)5ULL);
v___x_864_ = lean_usize_shift_right(v_x_825_, v___x_863_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_x_826_, v___x_865_);
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_859_, v___x_864_, v___x_866_, v_x_827_, v_x_828_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_867_);
v___x_869_ = v___x_861_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v___y_842_ = v___x_869_;
goto v___jp_841_;
}
}
}
default: 
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_x_827_);
lean_ctor_set(v___x_872_, 1, v_x_828_);
v___y_842_ = v___x_872_;
goto v___jp_841_;
}
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_array_fset(v_xs_x27_840_, v_j_832_, v___y_842_);
lean_dec(v_j_832_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v_ks_875_; lean_object* v_vs_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_896_; 
v_ks_875_ = lean_ctor_get(v_x_824_, 0);
v_vs_876_ = lean_ctor_get(v_x_824_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_x_824_);
if (v_isSharedCheck_896_ == 0)
{
v___x_878_ = v_x_824_;
v_isShared_879_ = v_isSharedCheck_896_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_vs_876_);
lean_inc(v_ks_875_);
lean_dec(v_x_824_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_896_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_ks_875_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_vs_876_);
v___x_881_ = v_reuseFailAlloc_895_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v_newNode_882_; uint8_t v___y_884_; size_t v___x_890_; uint8_t v___x_891_; 
v_newNode_882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_881_, v_x_827_, v_x_828_);
v___x_890_ = ((size_t)7ULL);
v___x_891_ = lean_usize_dec_le(v___x_890_, v_x_826_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_892_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_882_);
v___x_893_ = lean_unsigned_to_nat(4u);
v___x_894_ = lean_nat_dec_lt(v___x_892_, v___x_893_);
lean_dec(v___x_892_);
v___y_884_ = v___x_894_;
goto v___jp_883_;
}
else
{
v___y_884_ = v___x_891_;
goto v___jp_883_;
}
v___jp_883_:
{
if (v___y_884_ == 0)
{
lean_object* v_ks_885_; lean_object* v_vs_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_ks_885_ = lean_ctor_get(v_newNode_882_, 0);
lean_inc_ref(v_ks_885_);
v_vs_886_ = lean_ctor_get(v_newNode_882_, 1);
lean_inc_ref(v_vs_886_);
lean_dec_ref(v_newNode_882_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0);
v___x_889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_826_, v_ks_885_, v_vs_886_, v___x_887_, v___x_888_);
lean_dec_ref(v_vs_886_);
lean_dec_ref(v_ks_885_);
return v___x_889_;
}
else
{
return v_newNode_882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_897_, lean_object* v_keys_898_, lean_object* v_vals_899_, lean_object* v_i_900_, lean_object* v_entries_901_){
_start:
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_array_get_size(v_keys_898_);
v___x_903_ = lean_nat_dec_lt(v_i_900_, v___x_902_);
if (v___x_903_ == 0)
{
lean_dec(v_i_900_);
return v_entries_901_;
}
else
{
lean_object* v_k_904_; lean_object* v_v_905_; uint64_t v___y_907_; 
v_k_904_ = lean_array_fget_borrowed(v_keys_898_, v_i_900_);
v_v_905_ = lean_array_fget_borrowed(v_vals_899_, v_i_900_);
if (lean_obj_tag(v_k_904_) == 0)
{
uint64_t v___x_918_; 
v___x_918_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_907_ = v___x_918_;
goto v___jp_906_;
}
else
{
uint64_t v_hash_919_; 
v_hash_919_ = lean_ctor_get_uint64(v_k_904_, sizeof(void*)*2);
v___y_907_ = v_hash_919_;
goto v___jp_906_;
}
v___jp_906_:
{
size_t v_h_908_; size_t v___x_909_; lean_object* v___x_910_; size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v_h_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_h_908_ = lean_uint64_to_usize(v___y_907_);
v___x_909_ = ((size_t)5ULL);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_sub(v_depth_897_, v___x_911_);
v___x_913_ = lean_usize_mul(v___x_909_, v___x_912_);
v_h_914_ = lean_usize_shift_right(v_h_908_, v___x_913_);
v___x_915_ = lean_nat_add(v_i_900_, v___x_910_);
lean_dec(v_i_900_);
lean_inc(v_v_905_);
lean_inc(v_k_904_);
v___x_916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_901_, v_h_914_, v_depth_897_, v_k_904_, v_v_905_);
v_i_900_ = v___x_915_;
v_entries_901_ = v___x_916_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_920_, lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_i_923_, lean_object* v_entries_924_){
_start:
{
size_t v_depth_boxed_925_; lean_object* v_res_926_; 
v_depth_boxed_925_ = lean_unbox_usize(v_depth_920_);
lean_dec(v_depth_920_);
v_res_926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_925_, v_keys_921_, v_vals_922_, v_i_923_, v_entries_924_);
lean_dec_ref(v_vals_922_);
lean_dec_ref(v_keys_921_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
size_t v_x_2919__boxed_932_; size_t v_x_2920__boxed_933_; lean_object* v_res_934_; 
v_x_2919__boxed_932_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_x_2920__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_res_934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_927_, v_x_2919__boxed_932_, v_x_2920__boxed_933_, v_x_930_, v_x_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
uint64_t v___y_939_; 
if (lean_obj_tag(v_x_936_) == 0)
{
uint64_t v___x_943_; 
v___x_943_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_939_ = v___x_943_;
goto v___jp_938_;
}
else
{
uint64_t v_hash_944_; 
v_hash_944_ = lean_ctor_get_uint64(v_x_936_, sizeof(void*)*2);
v___y_939_ = v_hash_944_;
goto v___jp_938_;
}
v___jp_938_:
{
size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_uint64_to_usize(v___y_939_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_935_, v___x_940_, v___x_941_, v_x_936_, v_x_937_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object* v_xs_945_, lean_object* v_v_946_, lean_object* v_i_947_){
_start:
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_array_get_size(v_xs_945_);
v___x_949_ = lean_nat_dec_lt(v_i_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v_i_947_);
v___x_950_ = lean_box(0);
return v___x_950_;
}
else
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_array_fget_borrowed(v_xs_945_, v_i_947_);
v___x_952_ = lean_name_eq(v___x_951_, v_v_946_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_i_947_, v___x_953_);
lean_dec(v_i_947_);
v_i_947_ = v___x_954_;
goto _start;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_i_947_);
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_xs_957_, lean_object* v_v_958_, lean_object* v_i_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_957_, v_v_958_, v_i_959_);
lean_dec(v_v_958_);
lean_dec_ref(v_xs_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object* v_xs_961_, lean_object* v_v_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_961_, v_v_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object* v_xs_965_, lean_object* v_v_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_965_, v_v_966_);
lean_dec(v_v_966_);
lean_dec_ref(v_xs_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object* v_x_968_, size_t v_x_969_, lean_object* v_x_970_){
_start:
{
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v_es_971_; lean_object* v___x_972_; size_t v___x_973_; size_t v___x_974_; lean_object* v_j_975_; lean_object* v_entry_976_; 
v_es_971_ = lean_ctor_get(v_x_968_, 0);
v___x_972_ = lean_box(2);
v___x_973_ = ((size_t)31ULL);
v___x_974_ = lean_usize_land(v_x_969_, v___x_973_);
v_j_975_ = lean_usize_to_nat(v___x_974_);
v_entry_976_ = lean_array_get(v___x_972_, v_es_971_, v_j_975_);
switch(lean_obj_tag(v_entry_976_))
{
case 0:
{
lean_object* v_key_977_; uint8_t v___x_978_; 
v_key_977_ = lean_ctor_get(v_entry_976_, 0);
lean_inc(v_key_977_);
lean_dec_ref_known(v_entry_976_, 2);
v___x_978_ = lean_name_eq(v_x_970_, v_key_977_);
lean_dec(v_key_977_);
if (v___x_978_ == 0)
{
lean_dec(v_j_975_);
return v_x_968_;
}
else
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
lean_inc_ref(v_es_971_);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; 
v_unused_987_ = lean_ctor_get(v_x_968_, 0);
lean_dec(v_unused_987_);
v___x_980_ = v_x_968_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_dec(v_x_968_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_array_set(v_es_971_, v_j_975_, v___x_972_);
lean_dec(v_j_975_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
case 1:
{
lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1022_; 
lean_inc_ref(v_es_971_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_x_968_, 0);
lean_dec(v_unused_1023_);
v___x_989_ = v_x_968_;
v_isShared_990_ = v_isSharedCheck_1022_;
goto v_resetjp_988_;
}
else
{
lean_dec(v_x_968_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1022_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_node_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1021_; 
v_node_991_ = lean_ctor_get(v_entry_976_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_entry_976_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_993_ = v_entry_976_;
v_isShared_994_ = v_isSharedCheck_1021_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_node_991_);
lean_dec(v_entry_976_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1021_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
size_t v___x_995_; lean_object* v_entries_996_; size_t v___x_997_; lean_object* v_newNode_998_; lean_object* v___x_999_; 
v___x_995_ = ((size_t)5ULL);
v_entries_996_ = lean_array_set(v_es_971_, v_j_975_, v___x_972_);
v___x_997_ = lean_usize_shift_right(v_x_969_, v___x_995_);
v_newNode_998_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_991_, v___x_997_, v_x_970_);
lean_inc_ref(v_newNode_998_);
v___x_999_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1001_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_newNode_998_);
v___x_1001_ = v___x_993_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_newNode_998_);
v___x_1001_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_array_set(v_entries_996_, v_j_975_, v___x_1001_);
lean_dec(v_j_975_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1002_);
v___x_1004_ = v___x_989_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v_val_1007_; lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_newNode_998_);
lean_del_object(v___x_993_);
v_val_1007_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v___x_999_, 1);
v_fst_1008_ = lean_ctor_get(v_val_1007_, 0);
v_snd_1009_ = lean_ctor_get(v_val_1007_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_val_1007_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1011_ = v_val_1007_;
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_inc(v_fst_1008_);
lean_dec(v_val_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_fst_1008_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_snd_1009_);
v___x_1014_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_array_set(v_entries_996_, v_j_975_, v___x_1014_);
lean_dec(v_j_975_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1015_);
v___x_1017_ = v___x_989_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_975_);
return v_x_968_;
}
}
}
else
{
lean_object* v_ks_1024_; lean_object* v_vs_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1039_; 
v_ks_1024_ = lean_ctor_get(v_x_968_, 0);
v_vs_1025_ = lean_ctor_get(v_x_968_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1027_ = v_x_968_;
v_isShared_1028_ = v_isSharedCheck_1039_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_vs_1025_);
lean_inc(v_ks_1024_);
lean_dec(v_x_968_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1039_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_1024_, v_x_970_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1031_; 
if (v_isShared_1028_ == 0)
{
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_ks_1024_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_vs_1025_);
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
lean_object* v_val_1033_; lean_object* v_keys_x27_1034_; lean_object* v_vals_x27_1035_; lean_object* v___x_1037_; 
v_val_1033_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_n(v_val_1033_, 2);
lean_dec_ref_known(v___x_1029_, 1);
v_keys_x27_1034_ = l_Array_eraseIdx___redArg(v_ks_1024_, v_val_1033_);
v_vals_x27_1035_ = l_Array_eraseIdx___redArg(v_vs_1025_, v_val_1033_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 1, v_vals_x27_1035_);
lean_ctor_set(v___x_1027_, 0, v_keys_x27_1034_);
v___x_1037_ = v___x_1027_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_keys_x27_1034_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_vals_x27_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
size_t v_x_3122__boxed_1043_; lean_object* v_res_1044_; 
v_x_3122__boxed_1043_ = lean_unbox_usize(v_x_1041_);
lean_dec(v_x_1041_);
v_res_1044_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1040_, v_x_3122__boxed_1043_, v_x_1042_);
lean_dec(v_x_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
uint64_t v___y_1048_; 
if (lean_obj_tag(v_x_1046_) == 0)
{
uint64_t v___x_1051_; 
v___x_1051_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1048_ = v___x_1051_;
goto v___jp_1047_;
}
else
{
uint64_t v_hash_1052_; 
v_hash_1052_ = lean_ctor_get_uint64(v_x_1046_, sizeof(void*)*2);
v___y_1048_ = v_hash_1052_;
goto v___jp_1047_;
}
v___jp_1047_:
{
size_t v_h_1049_; lean_object* v___x_1050_; 
v_h_1049_ = lean_uint64_to_usize(v___y_1048_);
v___x_1050_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1045_, v_h_1049_, v_x_1046_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1053_, v_x_1054_);
lean_dec(v_x_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object* v_s_1056_, lean_object* v_keys_1057_, lean_object* v_declName_1058_, uint8_t v_phase_1059_, lean_object* v_proc_1060_){
_start:
{
lean_object* v_pre_1061_; lean_object* v_eval_1062_; lean_object* v_post_1063_; lean_object* v_simprocNames_1064_; lean_object* v_erased_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1086_; 
v_pre_1061_ = lean_ctor_get(v_s_1056_, 0);
v_eval_1062_ = lean_ctor_get(v_s_1056_, 1);
v_post_1063_ = lean_ctor_get(v_s_1056_, 2);
v_simprocNames_1064_ = lean_ctor_get(v_s_1056_, 3);
v_erased_1065_ = lean_ctor_get(v_s_1056_, 4);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_s_1056_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1067_ = v_s_1056_;
v_isShared_1068_ = v_isSharedCheck_1086_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_erased_1065_);
lean_inc(v_simprocNames_1064_);
lean_inc(v_post_1063_);
lean_inc(v_eval_1062_);
lean_inc(v_pre_1061_);
lean_dec(v_s_1056_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1086_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v_entry_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_inc_ref(v_keys_1057_);
lean_inc_n(v_declName_1058_, 2);
v___x_1069_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1069_, 0, v_declName_1058_);
lean_ctor_set(v___x_1069_, 1, v_keys_1057_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*2, v_phase_1059_);
v_entry_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_entry_1070_, 0, v___x_1069_);
lean_ctor_set(v_entry_1070_, 1, v_proc_1060_);
v___x_1071_ = lean_box(0);
v___x_1072_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_1064_, v_declName_1058_, v___x_1071_);
v___x_1073_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_1065_, v_declName_1058_);
lean_dec(v_declName_1058_);
switch(v_phase_1059_)
{
case 0:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_1061_, v_keys_1057_, v_entry_1070_);
lean_dec_ref(v_keys_1057_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v___x_1073_);
lean_ctor_set(v___x_1067_, 3, v___x_1072_);
lean_ctor_set(v___x_1067_, 0, v___x_1074_);
v___x_1076_ = v___x_1067_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_eval_1062_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_post_1063_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___x_1073_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
case 1:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_1062_, v_keys_1057_, v_entry_1070_);
lean_dec_ref(v_keys_1057_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v___x_1073_);
lean_ctor_set(v___x_1067_, 3, v___x_1072_);
lean_ctor_set(v___x_1067_, 1, v___x_1078_);
v___x_1080_ = v___x_1067_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_pre_1061_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_post_1063_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___x_1073_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
default: 
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_1063_, v_keys_1057_, v_entry_1070_);
lean_dec_ref(v_keys_1057_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v___x_1073_);
lean_ctor_set(v___x_1067_, 3, v___x_1072_);
lean_ctor_set(v___x_1067_, 2, v___x_1082_);
v___x_1084_ = v___x_1067_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_pre_1061_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_eval_1062_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v___x_1073_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object* v_s_1087_, lean_object* v_keys_1088_, lean_object* v_declName_1089_, lean_object* v_phase_1090_, lean_object* v_proc_1091_){
_start:
{
uint8_t v_phase_boxed_1092_; lean_object* v_res_1093_; 
v_phase_boxed_1092_ = lean_unbox(v_phase_1090_);
v_res_1093_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_1087_, v_keys_1088_, v_declName_1089_, v_phase_boxed_1092_, v_proc_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_1095_, v_x_1096_, v_x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object* v_00_u03b2_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1100_, v_x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object* v_00_u03b2_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(v_00_u03b2_1103_, v_x_1104_, v_x_1105_);
lean_dec(v_x_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, size_t v_x_1109_, size_t v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1108_, v_x_1109_, v_x_1110_, v_x_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
size_t v_x_3331__boxed_1120_; size_t v_x_3332__boxed_1121_; lean_object* v_res_1122_; 
v_x_3331__boxed_1120_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_x_3332__boxed_1121_ = lean_unbox_usize(v_x_1117_);
lean_dec(v_x_1117_);
v_res_1122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_1114_, v_x_1115_, v_x_3331__boxed_1120_, v_x_3332__boxed_1121_, v_x_1118_, v_x_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object* v_00_u03b2_1123_, lean_object* v_x_1124_, size_t v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1124_, v_x_1125_, v_x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
size_t v_x_3348__boxed_1132_; lean_object* v_res_1133_; 
v_x_3348__boxed_1132_ = lean_unbox_usize(v_x_1130_);
lean_dec(v_x_1130_);
v_res_1133_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_1128_, v_x_1129_, v_x_3348__boxed_1132_, v_x_1131_);
lean_dec(v_x_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1134_, lean_object* v_n_1135_, lean_object* v_k_1136_, lean_object* v_v_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_1135_, v_k_1136_, v_v_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1139_, size_t v_depth_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_heq_1143_, lean_object* v_i_1144_, lean_object* v_entries_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_1140_, v_keys_1141_, v_vals_1142_, v_i_1144_, v_entries_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_depth_1148_, lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_heq_1151_, lean_object* v_i_1152_, lean_object* v_entries_1153_){
_start:
{
size_t v_depth_boxed_1154_; lean_object* v_res_1155_; 
v_depth_boxed_1154_ = lean_unbox_usize(v_depth_1148_);
lean_dec(v_depth_1148_);
v_res_1155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_1147_, v_depth_boxed_1154_, v_keys_1149_, v_vals_1150_, v_heq_1151_, v_i_1152_, v_entries_1153_);
lean_dec_ref(v_vals_1150_);
lean_dec_ref(v_keys_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(lean_object* v_00_u03b2_1156_, lean_object* v_x_1157_, size_t v_x_1158_, size_t v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_x_1157_, v_x_1158_, v_x_1159_, v_x_1160_, v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_){
_start:
{
size_t v_x_3363__boxed_1169_; size_t v_x_3364__boxed_1170_; lean_object* v_res_1171_; 
v_x_3363__boxed_1169_ = lean_unbox_usize(v_x_1165_);
lean_dec(v_x_1165_);
v_x_3364__boxed_1170_ = lean_unbox_usize(v_x_1166_);
lean_dec(v_x_1166_);
v_res_1171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(v_00_u03b2_1163_, v_x_1164_, v_x_3363__boxed_1169_, v_x_3364__boxed_1170_, v_x_1167_, v_x_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1173_, v_x_1174_, v_x_1175_, v_x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(lean_object* v_x_1178_, lean_object* v_keys_1179_, lean_object* v_v_1180_, lean_object* v_k_1181_, lean_object* v_as_1182_, lean_object* v_k_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_1178_, v_keys_1179_, v_v_1180_, v_k_1181_, v_as_1182_, v_k_1183_, v_x_1184_, v_x_1185_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___boxed(lean_object* v_x_1189_, lean_object* v_keys_1190_, lean_object* v_v_1191_, lean_object* v_k_1192_, lean_object* v_as_1193_, lean_object* v_k_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(v_x_1189_, v_keys_1190_, v_v_1191_, v_k_1192_, v_as_1193_, v_k_1194_, v_x_1195_, v_x_1196_, v_x_1197_, v_x_1198_);
lean_dec_ref(v_k_1194_);
lean_dec_ref(v_keys_1190_);
lean_dec(v_x_1189_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(lean_object* v_00_u03b2_1200_, lean_object* v_n_1201_, lean_object* v_k_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(v_n_1201_, v_k_1202_, v_v_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(lean_object* v_00_u03b2_1205_, size_t v_depth_1206_, lean_object* v_keys_1207_, lean_object* v_vals_1208_, lean_object* v_heq_1209_, lean_object* v_i_1210_, lean_object* v_entries_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_depth_1206_, v_keys_1207_, v_vals_1208_, v_i_1210_, v_entries_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___boxed(lean_object* v_00_u03b2_1213_, lean_object* v_depth_1214_, lean_object* v_keys_1215_, lean_object* v_vals_1216_, lean_object* v_heq_1217_, lean_object* v_i_1218_, lean_object* v_entries_1219_){
_start:
{
size_t v_depth_boxed_1220_; lean_object* v_res_1221_; 
v_depth_boxed_1220_ = lean_unbox_usize(v_depth_1214_);
lean_dec(v_depth_1214_);
v_res_1221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(v_00_u03b2_1213_, v_depth_boxed_1220_, v_keys_1215_, v_vals_1216_, v_heq_1217_, v_i_1218_, v_entries_1219_);
lean_dec_ref(v_vals_1216_);
lean_dec_ref(v_keys_1215_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20(lean_object* v_00_u03b2_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(v_x_1223_, v_x_1224_, v_x_1225_, v_x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object* v_s_1228_, lean_object* v_declName_1229_){
_start:
{
lean_object* v_pre_1230_; lean_object* v_eval_1231_; lean_object* v_post_1232_; lean_object* v_simprocNames_1233_; lean_object* v_erased_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1244_; 
v_pre_1230_ = lean_ctor_get(v_s_1228_, 0);
v_eval_1231_ = lean_ctor_get(v_s_1228_, 1);
v_post_1232_ = lean_ctor_get(v_s_1228_, 2);
v_simprocNames_1233_ = lean_ctor_get(v_s_1228_, 3);
v_erased_1234_ = lean_ctor_get(v_s_1228_, 4);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_s_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1236_ = v_s_1228_;
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_erased_1234_);
lean_inc(v_simprocNames_1233_);
lean_inc(v_post_1232_);
lean_inc(v_eval_1231_);
lean_inc(v_pre_1230_);
lean_dec(v_s_1228_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1238_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_1233_, v_declName_1229_);
v___x_1239_ = lean_box(0);
v___x_1240_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_1234_, v_declName_1229_, v___x_1239_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 4, v___x_1240_);
lean_ctor_set(v___x_1236_, 3, v___x_1238_);
v___x_1242_ = v___x_1236_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_pre_1230_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_eval_1231_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_post_1232_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_unsigned_to_nat(16u);
v___x_1247_ = lean_mk_array(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default(void){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs(void){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1257_ = lean_st_mk_ref(v___x_1256_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
return v_res_1260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object* v_a_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = 0;
return v___x_1263_;
}
else
{
lean_object* v_key_1264_; lean_object* v_tail_1265_; uint8_t v___x_1266_; 
v_key_1264_ = lean_ctor_get(v_x_1262_, 0);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v___x_1266_ = lean_name_eq(v_key_1264_, v_a_1261_);
if (v___x_1266_ == 0)
{
v_x_1262_ = v_tail_1265_;
goto _start;
}
else
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_1268_, lean_object* v_x_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1268_, v_x_1269_);
lean_dec(v_x_1269_);
lean_dec(v_a_1268_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object* v_m_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_buckets_1274_; lean_object* v___x_1275_; uint64_t v___y_1277_; 
v_buckets_1274_ = lean_ctor_get(v_m_1272_, 1);
v___x_1275_ = lean_array_get_size(v_buckets_1274_);
if (lean_obj_tag(v_a_1273_) == 0)
{
uint64_t v___x_1291_; 
v___x_1291_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1277_ = v___x_1291_;
goto v___jp_1276_;
}
else
{
uint64_t v_hash_1292_; 
v_hash_1292_ = lean_ctor_get_uint64(v_a_1273_, sizeof(void*)*2);
v___y_1277_ = v_hash_1292_;
goto v___jp_1276_;
}
v___jp_1276_:
{
uint64_t v___x_1278_; uint64_t v___x_1279_; uint64_t v_fold_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1278_ = 32ULL;
v___x_1279_ = lean_uint64_shift_right(v___y_1277_, v___x_1278_);
v_fold_1280_ = lean_uint64_xor(v___y_1277_, v___x_1279_);
v___x_1281_ = 16ULL;
v___x_1282_ = lean_uint64_shift_right(v_fold_1280_, v___x_1281_);
v___x_1283_ = lean_uint64_xor(v_fold_1280_, v___x_1282_);
v___x_1284_ = lean_uint64_to_usize(v___x_1283_);
v___x_1285_ = lean_usize_of_nat(v___x_1275_);
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = lean_usize_sub(v___x_1285_, v___x_1286_);
v___x_1288_ = lean_usize_land(v___x_1284_, v___x_1287_);
v___x_1289_ = lean_array_uget_borrowed(v_buckets_1274_, v___x_1288_);
v___x_1290_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1273_, v___x_1289_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object* v_m_1293_, lean_object* v_a_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1293_, v_a_1294_);
lean_dec(v_a_1294_);
lean_dec_ref(v_m_1293_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
lean_dec(v_b_1298_);
lean_dec(v_a_1297_);
return v_x_1299_;
}
else
{
lean_object* v_key_1300_; lean_object* v_value_1301_; lean_object* v_tail_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1314_; 
v_key_1300_ = lean_ctor_get(v_x_1299_, 0);
v_value_1301_ = lean_ctor_get(v_x_1299_, 1);
v_tail_1302_ = lean_ctor_get(v_x_1299_, 2);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_x_1299_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1304_ = v_x_1299_;
v_isShared_1305_ = v_isSharedCheck_1314_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_tail_1302_);
lean_inc(v_value_1301_);
lean_inc(v_key_1300_);
lean_dec(v_x_1299_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1314_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_name_eq(v_key_1300_, v_a_1297_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1297_, v_b_1298_, v_tail_1302_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 2, v___x_1307_);
v___x_1309_ = v___x_1304_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_key_1300_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_value_1301_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
lean_object* v___x_1312_; 
lean_dec(v_value_1301_);
lean_dec(v_key_1300_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v_b_1298_);
lean_ctor_set(v___x_1304_, 0, v_a_1297_);
v___x_1312_ = v___x_1304_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1297_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_b_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_tail_1302_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 0)
{
return v_x_1315_;
}
else
{
lean_object* v_key_1317_; lean_object* v_value_1318_; lean_object* v_tail_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1345_; 
v_key_1317_ = lean_ctor_get(v_x_1316_, 0);
v_value_1318_ = lean_ctor_get(v_x_1316_, 1);
v_tail_1319_ = lean_ctor_get(v_x_1316_, 2);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_x_1316_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1321_ = v_x_1316_;
v_isShared_1322_ = v_isSharedCheck_1345_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_tail_1319_);
lean_inc(v_value_1318_);
lean_inc(v_key_1317_);
lean_dec(v_x_1316_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1345_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; uint64_t v___y_1325_; 
v___x_1323_ = lean_array_get_size(v_x_1315_);
if (lean_obj_tag(v_key_1317_) == 0)
{
uint64_t v___x_1343_; 
v___x_1343_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1325_ = v___x_1343_;
goto v___jp_1324_;
}
else
{
uint64_t v_hash_1344_; 
v_hash_1344_ = lean_ctor_get_uint64(v_key_1317_, sizeof(void*)*2);
v___y_1325_ = v_hash_1344_;
goto v___jp_1324_;
}
v___jp_1324_:
{
uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v_fold_1328_; uint64_t v___x_1329_; uint64_t v___x_1330_; uint64_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1326_ = 32ULL;
v___x_1327_ = lean_uint64_shift_right(v___y_1325_, v___x_1326_);
v_fold_1328_ = lean_uint64_xor(v___y_1325_, v___x_1327_);
v___x_1329_ = 16ULL;
v___x_1330_ = lean_uint64_shift_right(v_fold_1328_, v___x_1329_);
v___x_1331_ = lean_uint64_xor(v_fold_1328_, v___x_1330_);
v___x_1332_ = lean_uint64_to_usize(v___x_1331_);
v___x_1333_ = lean_usize_of_nat(v___x_1323_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_sub(v___x_1333_, v___x_1334_);
v___x_1336_ = lean_usize_land(v___x_1332_, v___x_1335_);
v___x_1337_ = lean_array_uget_borrowed(v_x_1315_, v___x_1336_);
lean_inc(v___x_1337_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 2, v___x_1337_);
v___x_1339_ = v___x_1321_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_key_1317_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_value_1318_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_array_uset(v_x_1315_, v___x_1336_, v___x_1339_);
v_x_1315_ = v___x_1340_;
v_x_1316_ = v_tail_1319_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1346_, lean_object* v_source_1347_, lean_object* v_target_1348_){
_start:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = lean_array_get_size(v_source_1347_);
v___x_1350_ = lean_nat_dec_lt(v_i_1346_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v_source_1347_);
lean_dec(v_i_1346_);
return v_target_1348_;
}
else
{
lean_object* v_es_1351_; lean_object* v___x_1352_; lean_object* v_source_1353_; lean_object* v_target_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_es_1351_ = lean_array_fget(v_source_1347_, v_i_1346_);
v___x_1352_ = lean_box(0);
v_source_1353_ = lean_array_fset(v_source_1347_, v_i_1346_, v___x_1352_);
v_target_1354_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1348_, v_es_1351_);
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_add(v_i_1346_, v___x_1355_);
lean_dec(v_i_1346_);
v_i_1346_ = v___x_1356_;
v_source_1347_ = v_source_1353_;
v_target_1348_ = v_target_1354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object* v_data_1358_){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_nbuckets_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1359_ = lean_array_get_size(v_data_1358_);
v___x_1360_ = lean_unsigned_to_nat(2u);
v_nbuckets_1361_ = lean_nat_mul(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_mk_array(v_nbuckets_1361_, v___x_1363_);
v___x_1365_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v___x_1362_, v_data_1358_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object* v_m_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_){
_start:
{
lean_object* v_size_1369_; lean_object* v_buckets_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1416_; 
v_size_1369_ = lean_ctor_get(v_m_1366_, 0);
v_buckets_1370_ = lean_ctor_get(v_m_1366_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_m_1366_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1372_ = v_m_1366_;
v_isShared_1373_ = v_isSharedCheck_1416_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_buckets_1370_);
lean_inc(v_size_1369_);
lean_dec(v_m_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1416_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; uint64_t v___y_1376_; 
v___x_1374_ = lean_array_get_size(v_buckets_1370_);
if (lean_obj_tag(v_a_1367_) == 0)
{
uint64_t v___x_1414_; 
v___x_1414_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1376_ = v___x_1414_;
goto v___jp_1375_;
}
else
{
uint64_t v_hash_1415_; 
v_hash_1415_ = lean_ctor_get_uint64(v_a_1367_, sizeof(void*)*2);
v___y_1376_ = v_hash_1415_;
goto v___jp_1375_;
}
v___jp_1375_:
{
uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v_fold_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v_bkt_1388_; uint8_t v___x_1389_; 
v___x_1377_ = 32ULL;
v___x_1378_ = lean_uint64_shift_right(v___y_1376_, v___x_1377_);
v_fold_1379_ = lean_uint64_xor(v___y_1376_, v___x_1378_);
v___x_1380_ = 16ULL;
v___x_1381_ = lean_uint64_shift_right(v_fold_1379_, v___x_1380_);
v___x_1382_ = lean_uint64_xor(v_fold_1379_, v___x_1381_);
v___x_1383_ = lean_uint64_to_usize(v___x_1382_);
v___x_1384_ = lean_usize_of_nat(v___x_1374_);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_sub(v___x_1384_, v___x_1385_);
v___x_1387_ = lean_usize_land(v___x_1383_, v___x_1386_);
v_bkt_1388_ = lean_array_uget_borrowed(v_buckets_1370_, v___x_1387_);
v___x_1389_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1367_, v_bkt_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v_size_x27_1391_; lean_object* v___x_1392_; lean_object* v_buckets_x27_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1390_ = lean_unsigned_to_nat(1u);
v_size_x27_1391_ = lean_nat_add(v_size_1369_, v___x_1390_);
lean_dec(v_size_1369_);
lean_inc(v_bkt_1388_);
v___x_1392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1392_, 0, v_a_1367_);
lean_ctor_set(v___x_1392_, 1, v_b_1368_);
lean_ctor_set(v___x_1392_, 2, v_bkt_1388_);
v_buckets_x27_1393_ = lean_array_uset(v_buckets_1370_, v___x_1387_, v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(4u);
v___x_1395_ = lean_nat_mul(v_size_x27_1391_, v___x_1394_);
v___x_1396_ = lean_unsigned_to_nat(3u);
v___x_1397_ = lean_nat_div(v___x_1395_, v___x_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_array_get_size(v_buckets_x27_1393_);
v___x_1399_ = lean_nat_dec_le(v___x_1397_, v___x_1398_);
lean_dec(v___x_1397_);
if (v___x_1399_ == 0)
{
lean_object* v_val_1400_; lean_object* v___x_1402_; 
v_val_1400_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_buckets_x27_1393_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_val_1400_);
lean_ctor_set(v___x_1372_, 0, v_size_x27_1391_);
v___x_1402_ = v___x_1372_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_size_x27_1391_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_val_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1405_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_buckets_x27_1393_);
lean_ctor_set(v___x_1372_, 0, v_size_x27_1391_);
v___x_1405_ = v___x_1372_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_size_x27_1391_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_buckets_x27_1393_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_object* v___x_1407_; lean_object* v_buckets_x27_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc(v_bkt_1388_);
v___x_1407_ = lean_box(0);
v_buckets_x27_1408_ = lean_array_uset(v_buckets_1370_, v___x_1387_, v___x_1407_);
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1367_, v_b_1368_, v_bkt_1388_);
v___x_1410_ = lean_array_uset(v_buckets_x27_1408_, v___x_1387_, v___x_1409_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1410_);
v___x_1412_ = v___x_1372_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_size_1369_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0));
v___x_1419_ = lean_mk_io_user_error(v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object* v_declName_1422_, lean_object* v_keys_1423_, lean_object* v_proc_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1466_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1466_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1466_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_unbox(v_a_1427_);
lean_dec(v_a_1427_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec_ref(v_proc_1424_);
lean_dec_ref(v_keys_1423_);
lean_dec(v_declName_1422_);
v___x_1432_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
lean_ctor_set(v___x_1429_, 0, v___x_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_keys_1438_; uint8_t v___x_1439_; 
v___x_1436_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_1437_ = lean_st_ref_get(v___x_1436_);
v_keys_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_keys_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_1438_, v_declName_1422_);
lean_dec_ref(v_keys_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v_keys_1441_; lean_object* v_procs_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1455_; 
v___x_1440_ = lean_st_ref_take(v___x_1436_);
v_keys_1441_ = lean_ctor_get(v___x_1440_, 0);
v_procs_1442_ = lean_ctor_get(v___x_1440_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1444_ = v___x_1440_;
v_isShared_1445_ = v_isSharedCheck_1455_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_procs_1442_);
lean_inc(v_keys_1441_);
lean_dec(v___x_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1455_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_inc(v_declName_1422_);
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_1441_, v_declName_1422_, v_keys_1423_);
v___x_1447_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_1442_, v_declName_1422_, v_proc_1424_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1447_);
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_st_ref_set(v___x_1436_, v___x_1449_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1450_);
v___x_1452_ = v___x_1429_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec_ref(v_proc_1424_);
lean_dec_ref(v_keys_1423_);
v___x_1456_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2));
v___x_1457_ = l_Lean_privateToUserName(v_declName_1422_);
v___x_1458_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1457_, v___x_1439_);
v___x_1459_ = lean_string_append(v___x_1456_, v___x_1458_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_1461_ = lean_string_append(v___x_1459_, v___x_1460_);
v___x_1462_ = lean_mk_io_user_error(v___x_1461_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
lean_ctor_set(v___x_1429_, 0, v___x_1462_);
v___x_1464_ = v___x_1429_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_proc_1424_);
lean_dec_ref(v_keys_1423_);
lean_dec(v_declName_1422_);
v_a_1467_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1426_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1426_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object* v_declName_1475_, lean_object* v_keys_1476_, lean_object* v_proc_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1475_, v_keys_1476_, v_proc_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object* v_00_u03b2_1480_, lean_object* v_m_1481_, lean_object* v_a_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1481_, v_a_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object* v_00_u03b2_1484_, lean_object* v_m_1485_, lean_object* v_a_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_1484_, v_m_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_m_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object* v_00_u03b2_1489_, lean_object* v_m_1490_, lean_object* v_a_1491_, lean_object* v_b_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1490_, v_a_1491_, v_b_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object* v_00_u03b2_1494_, lean_object* v_a_1495_, lean_object* v_x_1496_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1495_, v_x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1498_, lean_object* v_a_1499_, lean_object* v_x_1500_){
_start:
{
uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_res_1501_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_1498_, v_a_1499_, v_x_1500_);
lean_dec(v_x_1500_);
lean_dec(v_a_1499_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object* v_00_u03b2_1503_, lean_object* v_data_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_data_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object* v_00_u03b2_1506_, lean_object* v_a_1507_, lean_object* v_b_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1507_, v_b_1508_, v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1511_, lean_object* v_i_1512_, lean_object* v_source_1513_, lean_object* v_target_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v_i_1512_, v_source_1513_, v_target_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1517_, v_x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object* v_d_u2081_1527_, lean_object* v_d_u2082_1528_){
_start:
{
lean_object* v_declName_1529_; lean_object* v_declName_1530_; uint8_t v___x_1531_; 
v_declName_1529_ = lean_ctor_get(v_d_u2081_1527_, 0);
v_declName_1530_ = lean_ctor_get(v_d_u2082_1528_, 0);
v___x_1531_ = l_Lean_Name_quickLt(v_declName_1529_, v_declName_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object* v_d_u2081_1532_, lean_object* v_d_u2082_1533_){
_start:
{
uint8_t v_res_1534_; lean_object* v_r_1535_; 
v_res_1534_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1532_, v_d_u2082_1533_);
lean_dec_ref(v_d_u2082_1533_);
lean_dec_ref(v_d_u2081_1532_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
v___x_1540_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___x_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState(void){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_s_1544_, lean_object* v_d_1545_){
_start:
{
lean_object* v_builtin_1546_; lean_object* v_newEntries_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1557_; 
v_builtin_1546_ = lean_ctor_get(v_s_1544_, 0);
v_newEntries_1547_ = lean_ctor_get(v_s_1544_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_s_1544_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1549_ = v_s_1544_;
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_newEntries_1547_);
lean_inc(v_builtin_1546_);
lean_dec(v_s_1544_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_declName_1551_; lean_object* v_keys_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v_declName_1551_ = lean_ctor_get(v_d_1545_, 0);
lean_inc(v_declName_1551_);
v_keys_1552_ = lean_ctor_get(v_d_1545_, 1);
lean_inc_ref(v_keys_1552_);
lean_dec_ref(v_d_1545_);
v___x_1553_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_1547_, v_declName_1551_, v_keys_1552_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v___x_1553_);
v___x_1555_ = v___x_1549_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_builtin_1546_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_result_1558_, lean_object* v_declName_1559_, lean_object* v_keys_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_declName_1559_);
lean_ctor_set(v___x_1561_, 1, v_keys_1560_);
v___x_1562_ = lean_array_push(v_result_1558_, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_1563_, lean_object* v_x1_1564_, lean_object* v_x2_1565_, lean_object* v_x3_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_apply_3(v_f_1563_, v_x1_1564_, v_x2_1565_, v_x3_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_1568_, lean_object* v_keys_1569_, lean_object* v_vals_1570_, lean_object* v_i_1571_, lean_object* v_acc_1572_){
_start:
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_array_get_size(v_keys_1569_);
v___x_1574_ = lean_nat_dec_lt(v_i_1571_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_dec(v_i_1571_);
lean_dec(v_f_1568_);
return v_acc_1572_;
}
else
{
lean_object* v_k_1575_; lean_object* v_v_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_k_1575_ = lean_array_fget_borrowed(v_keys_1569_, v_i_1571_);
v_v_1576_ = lean_array_fget_borrowed(v_vals_1570_, v_i_1571_);
lean_inc(v_f_1568_);
lean_inc(v_v_1576_);
lean_inc(v_k_1575_);
v___x_1577_ = lean_apply_3(v_f_1568_, v_acc_1572_, v_k_1575_, v_v_1576_);
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_i_1571_, v___x_1578_);
lean_dec(v_i_1571_);
v_i_1571_ = v___x_1579_;
v_acc_1572_ = v___x_1577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_1581_, lean_object* v_keys_1582_, lean_object* v_vals_1583_, lean_object* v_i_1584_, lean_object* v_acc_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1581_, v_keys_1582_, v_vals_1583_, v_i_1584_, v_acc_1585_);
lean_dec_ref(v_vals_1583_);
lean_dec_ref(v_keys_1582_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
lean_object* v_es_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_es_1590_ = lean_ctor_get(v_x_1588_, 0);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_array_get_size(v_es_1590_);
v___x_1593_ = lean_nat_dec_lt(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_dec(v_f_1587_);
return v_x_1589_;
}
else
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_nat_dec_le(v___x_1592_, v___x_1592_);
if (v___x_1594_ == 0)
{
if (v___x_1593_ == 0)
{
lean_dec(v_f_1587_);
return v_x_1589_;
}
else
{
size_t v___x_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = lean_usize_of_nat(v___x_1592_);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1587_, v_es_1590_, v___x_1595_, v___x_1596_, v_x_1589_);
return v___x_1597_;
}
}
else
{
size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = lean_usize_of_nat(v___x_1592_);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1587_, v_es_1590_, v___x_1598_, v___x_1599_, v_x_1589_);
return v___x_1600_;
}
}
}
else
{
lean_object* v_ks_1601_; lean_object* v_vs_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_ks_1601_ = lean_ctor_get(v_x_1588_, 0);
v_vs_1602_ = lean_ctor_get(v_x_1588_, 1);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1587_, v_ks_1601_, v_vs_1602_, v___x_1603_, v_x_1589_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1605_, lean_object* v_as_1606_, size_t v_i_1607_, size_t v_stop_1608_, lean_object* v_b_1609_){
_start:
{
lean_object* v___y_1611_; uint8_t v___x_1615_; 
v___x_1615_ = lean_usize_dec_eq(v_i_1607_, v_stop_1608_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_array_uget_borrowed(v_as_1606_, v_i_1607_);
switch(lean_obj_tag(v___x_1616_))
{
case 0:
{
lean_object* v_key_1617_; lean_object* v_val_1618_; lean_object* v___x_1619_; 
v_key_1617_ = lean_ctor_get(v___x_1616_, 0);
v_val_1618_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_f_1605_);
lean_inc(v_val_1618_);
lean_inc(v_key_1617_);
v___x_1619_ = lean_apply_3(v_f_1605_, v_b_1609_, v_key_1617_, v_val_1618_);
v___y_1611_ = v___x_1619_;
goto v___jp_1610_;
}
case 1:
{
lean_object* v_node_1620_; lean_object* v___x_1621_; 
v_node_1620_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_f_1605_);
v___x_1621_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1605_, v_node_1620_, v_b_1609_);
v___y_1611_ = v___x_1621_;
goto v___jp_1610_;
}
default: 
{
v___y_1611_ = v_b_1609_;
goto v___jp_1610_;
}
}
}
else
{
lean_dec(v_f_1605_);
return v_b_1609_;
}
v___jp_1610_:
{
size_t v___x_1612_; size_t v___x_1613_; 
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1607_, v___x_1612_);
v_i_1607_ = v___x_1613_;
v_b_1609_ = v___y_1611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1622_, lean_object* v_as_1623_, lean_object* v_i_1624_, lean_object* v_stop_1625_, lean_object* v_b_1626_){
_start:
{
size_t v_i_boxed_1627_; size_t v_stop_boxed_1628_; lean_object* v_res_1629_; 
v_i_boxed_1627_ = lean_unbox_usize(v_i_1624_);
lean_dec(v_i_1624_);
v_stop_boxed_1628_ = lean_unbox_usize(v_stop_1625_);
lean_dec(v_stop_1625_);
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1622_, v_as_1623_, v_i_boxed_1627_, v_stop_boxed_1628_, v_b_1626_);
lean_dec_ref(v_as_1623_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1630_, v_x_1631_, v_x_1632_);
lean_dec_ref(v_x_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_1634_, lean_object* v_f_1635_, lean_object* v_init_1636_){
_start:
{
lean_object* v___f_1637_; lean_object* v___x_1638_; 
v___f_1637_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1637_, 0, v_f_1635_);
v___x_1638_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1637_, v_map_1634_, v_init_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_1639_, lean_object* v_f_1640_, lean_object* v_init_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1639_, v_f_1640_, v_init_1641_);
lean_dec_ref(v_map_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_1643_, lean_object* v_pivot_1644_, lean_object* v_as_1645_, lean_object* v_i_1646_, lean_object* v_k_1647_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_lt(v_k_1647_, v_hi_1643_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_k_1647_);
v___x_1649_ = lean_array_fswap(v_as_1645_, v_i_1646_, v_hi_1643_);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_i_1646_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = lean_array_fget_borrowed(v_as_1645_, v_k_1647_);
v___x_1652_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1651_, v_pivot_1644_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_add(v_k_1647_, v___x_1653_);
lean_dec(v_k_1647_);
v_k_1647_ = v___x_1654_;
goto _start;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = lean_array_fswap(v_as_1645_, v_i_1646_, v_k_1647_);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_add(v_i_1646_, v___x_1657_);
lean_dec(v_i_1646_);
v___x_1659_ = lean_nat_add(v_k_1647_, v___x_1657_);
lean_dec(v_k_1647_);
v_as_1645_ = v___x_1656_;
v_i_1646_ = v___x_1658_;
v_k_1647_ = v___x_1659_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_1661_, lean_object* v_pivot_1662_, lean_object* v_as_1663_, lean_object* v_i_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1661_, v_pivot_1662_, v_as_1663_, v_i_1664_, v_k_1665_);
lean_dec_ref(v_pivot_1662_);
lean_dec(v_hi_1661_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_1667_, lean_object* v_as_1668_, lean_object* v_lo_1669_, lean_object* v_hi_1670_){
_start:
{
lean_object* v___y_1672_; uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_lt(v_lo_1669_, v_hi_1670_);
if (v___x_1682_ == 0)
{
lean_dec(v_lo_1669_);
return v_as_1668_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_mid_1685_; lean_object* v___y_1687_; lean_object* v___y_1693_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1683_ = lean_nat_add(v_lo_1669_, v_hi_1670_);
v___x_1684_ = lean_unsigned_to_nat(1u);
v_mid_1685_ = lean_nat_shiftr(v___x_1683_, v___x_1684_);
lean_dec(v___x_1683_);
v___x_1698_ = lean_array_fget_borrowed(v_as_1668_, v_mid_1685_);
v___x_1699_ = lean_array_fget_borrowed(v_as_1668_, v_lo_1669_);
v___x_1700_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
v___y_1693_ = v_as_1668_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_array_fswap(v_as_1668_, v_lo_1669_, v_mid_1685_);
v___y_1693_ = v___x_1701_;
goto v___jp_1692_;
}
v___jp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1688_ = lean_array_fget_borrowed(v___y_1687_, v_mid_1685_);
v___x_1689_ = lean_array_fget_borrowed(v___y_1687_, v_hi_1670_);
v___x_1690_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_dec(v_mid_1685_);
v___y_1672_ = v___y_1687_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_array_fswap(v___y_1687_, v_mid_1685_, v_hi_1670_);
lean_dec(v_mid_1685_);
v___y_1672_ = v___x_1691_;
goto v___jp_1671_;
}
}
v___jp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = lean_array_fget_borrowed(v___y_1693_, v_hi_1670_);
v___x_1695_ = lean_array_fget_borrowed(v___y_1693_, v_lo_1669_);
v___x_1696_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
v___y_1687_ = v___y_1693_;
goto v___jp_1686_;
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_array_fswap(v___y_1693_, v_lo_1669_, v_hi_1670_);
v___y_1687_ = v___x_1697_;
goto v___jp_1686_;
}
}
}
v___jp_1671_:
{
lean_object* v_pivot_1673_; lean_object* v___x_1674_; lean_object* v_fst_1675_; lean_object* v_snd_1676_; uint8_t v___x_1677_; 
v_pivot_1673_ = lean_array_fget(v___y_1672_, v_hi_1670_);
lean_inc_n(v_lo_1669_, 2);
v___x_1674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1670_, v_pivot_1673_, v___y_1672_, v_lo_1669_, v_lo_1669_);
lean_dec(v_pivot_1673_);
v_fst_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_fst_1675_);
v_snd_1676_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_snd_1676_);
lean_dec_ref(v___x_1674_);
v___x_1677_ = lean_nat_dec_le(v_hi_1670_, v_fst_1675_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1667_, v_snd_1676_, v_lo_1669_, v_fst_1675_);
v___x_1679_ = lean_unsigned_to_nat(1u);
v___x_1680_ = lean_nat_add(v_fst_1675_, v___x_1679_);
lean_dec(v_fst_1675_);
v_as_1668_ = v___x_1678_;
v_lo_1669_ = v___x_1680_;
goto _start;
}
else
{
lean_dec(v_fst_1675_);
lean_dec(v_lo_1669_);
return v_snd_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_1702_, lean_object* v_as_1703_, lean_object* v_lo_1704_, lean_object* v_hi_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1702_, v_as_1703_, v_lo_1704_, v_hi_1705_);
lean_dec(v_hi_1705_);
lean_dec(v_n_1702_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1709_, lean_object* v_s_1710_){
_start:
{
lean_object* v_newEntries_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_result_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_newEntries_1711_ = lean_ctor_get(v_s_1710_, 1);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1714_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1711_, v___f_1709_, v___x_1713_);
v___x_1715_ = lean_array_get_size(v_result_1714_);
v___x_1716_ = lean_nat_dec_eq(v___x_1715_, v___x_1712_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___y_1720_; uint8_t v___x_1724_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_sub(v___x_1715_, v___x_1717_);
v___x_1724_ = lean_nat_dec_le(v___x_1712_, v___x_1718_);
if (v___x_1724_ == 0)
{
lean_inc(v___x_1718_);
v___y_1720_ = v___x_1718_;
goto v___jp_1719_;
}
else
{
v___y_1720_ = v___x_1712_;
goto v___jp_1719_;
}
v___jp_1719_:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_nat_dec_le(v___y_1720_, v___x_1718_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec(v___x_1718_);
lean_inc(v___y_1720_);
v___x_1722_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1715_, v_result_1714_, v___y_1720_, v___y_1720_);
lean_dec(v___y_1720_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1715_, v_result_1714_, v___y_1720_, v___x_1718_);
lean_dec(v___x_1718_);
return v___x_1723_;
}
}
}
else
{
return v_result_1714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1725_, lean_object* v_s_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1725_, v_s_1726_);
lean_dec_ref(v_s_1726_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_x_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_box(0);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_x_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_1730_);
lean_dec_ref(v_x_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1732_, lean_object* v_x_1733_, lean_object* v_s_1734_){
_start:
{
lean_object* v_newEntries_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_result_1738_; lean_object* v___x_1739_; lean_object* v___y_1741_; lean_object* v___y_1742_; uint8_t v___x_1745_; 
v_newEntries_1735_ = lean_ctor_get(v_s_1734_, 1);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1738_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1735_, v___f_1732_, v___x_1737_);
v___x_1739_ = lean_array_get_size(v_result_1738_);
v___x_1745_ = lean_nat_dec_eq(v___x_1739_, v___x_1736_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___y_1749_; uint8_t v___x_1751_; 
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_sub(v___x_1739_, v___x_1746_);
v___x_1751_ = lean_nat_dec_le(v___x_1736_, v___x_1747_);
if (v___x_1751_ == 0)
{
lean_inc(v___x_1747_);
v___y_1749_ = v___x_1747_;
goto v___jp_1748_;
}
else
{
v___y_1749_ = v___x_1736_;
goto v___jp_1748_;
}
v___jp_1748_:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_nat_dec_le(v___y_1749_, v___x_1747_);
if (v___x_1750_ == 0)
{
lean_dec(v___x_1747_);
lean_inc(v___y_1749_);
v___y_1741_ = v___y_1749_;
v___y_1742_ = v___y_1749_;
goto v___jp_1740_;
}
else
{
v___y_1741_ = v___y_1749_;
v___y_1742_ = v___x_1747_;
goto v___jp_1740_;
}
}
}
else
{
lean_object* v___x_1752_; 
lean_inc_n(v_result_1738_, 2);
v___x_1752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1752_, 0, v_result_1738_);
lean_ctor_set(v___x_1752_, 1, v_result_1738_);
lean_ctor_set(v___x_1752_, 2, v_result_1738_);
return v___x_1752_;
}
v___jp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1739_, v_result_1738_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_inc_ref_n(v___x_1743_, 2);
v___x_1744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
lean_ctor_set(v___x_1744_, 2, v___x_1743_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1753_, lean_object* v_x_1754_, lean_object* v_s_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1753_, v_x_1754_, v_s_1755_);
lean_dec_ref(v_s_1755_);
lean_dec_ref(v_x_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_keys_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1769_; 
v___x_1759_ = lean_st_ref_get(v___x_1757_);
v_keys_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1759_, 1);
lean_dec(v_unused_1770_);
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1769_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_keys_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1769_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_keys_1760_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1771_);
lean_dec(v___x_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; lean_object* v_keys_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1788_; 
v___x_1778_ = lean_st_ref_get(v___x_1774_);
v_keys_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1778_, 1);
lean_dec(v_unused_1789_);
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_keys_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 1, v___x_1783_);
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_keys_1779_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1790_, v_x_1791_, v___y_1792_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_x_1791_);
lean_dec(v___x_1790_);
return v_res_1794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___f_1810_; 
v___x_1809_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1810_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1810_, 0, v___x_1809_);
return v___f_1810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___f_1812_; 
v___x_1811_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_1812_, 0, v___x_1811_);
return v___f_1812_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___f_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1813_ = lean_box(0);
v___x_1814_ = lean_box(2);
v___f_1815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___f_1819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1821_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___f_1819_);
lean_ctor_set(v___x_1821_, 2, v___f_1818_);
lean_ctor_set(v___x_1821_, 3, v___f_1817_);
lean_ctor_set(v___x_1821_, 4, v___f_1816_);
lean_ctor_set(v___x_1821_, 5, v___f_1815_);
lean_ctor_set(v___x_1821_, 6, v___x_1814_);
lean_ctor_set(v___x_1821_, 7, v___x_1813_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___f_1822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___f_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1827_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_map_1832_, lean_object* v_f_1833_, lean_object* v_init_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1832_, v_f_1833_, v_init_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_map_1838_, lean_object* v_f_1839_, lean_object* v_init_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_1836_, v_00_u03b2_1837_, v_map_1838_, v_f_1839_, v_init_1840_);
lean_dec_ref(v_map_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object* v_n_1842_, lean_object* v_as_1843_, lean_object* v_lo_1844_, lean_object* v_hi_1845_, lean_object* v_w_1846_, lean_object* v_hlo_1847_, lean_object* v_hhi_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1842_, v_as_1843_, v_lo_1844_, v_hi_1845_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1850_, lean_object* v_as_1851_, lean_object* v_lo_1852_, lean_object* v_hi_1853_, lean_object* v_w_1854_, lean_object* v_hlo_1855_, lean_object* v_hhi_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_1850_, v_as_1851_, v_lo_1852_, v_hi_1853_, v_w_1854_, v_hlo_1855_, v_hhi_1856_);
lean_dec(v_hi_1853_);
lean_dec(v_n_1850_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_1858_, lean_object* v_f_1859_, lean_object* v_init_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1859_, v_map_1858_, v_init_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_1862_, lean_object* v_f_1863_, lean_object* v_init_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1862_, v_f_1863_, v_init_1864_);
lean_dec_ref(v_map_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_map_1868_, lean_object* v_f_1869_, lean_object* v_init_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1869_, v_map_1868_, v_init_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_1872_, lean_object* v_00_u03b2_1873_, lean_object* v_map_1874_, lean_object* v_f_1875_, lean_object* v_init_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1872_, v_00_u03b2_1873_, v_map_1874_, v_f_1875_, v_init_1876_);
lean_dec_ref(v_map_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_1878_, lean_object* v_lo_1879_, lean_object* v_hi_1880_, lean_object* v_hhi_1881_, lean_object* v_pivot_1882_, lean_object* v_as_1883_, lean_object* v_i_1884_, lean_object* v_k_1885_, lean_object* v_ilo_1886_, lean_object* v_ik_1887_, lean_object* v_w_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1880_, v_pivot_1882_, v_as_1883_, v_i_1884_, v_k_1885_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_1890_, lean_object* v_lo_1891_, lean_object* v_hi_1892_, lean_object* v_hhi_1893_, lean_object* v_pivot_1894_, lean_object* v_as_1895_, lean_object* v_i_1896_, lean_object* v_k_1897_, lean_object* v_ilo_1898_, lean_object* v_ik_1899_, lean_object* v_w_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(v_n_1890_, v_lo_1891_, v_hi_1892_, v_hhi_1893_, v_pivot_1894_, v_as_1895_, v_i_1896_, v_k_1897_, v_ilo_1898_, v_ik_1899_, v_w_1900_);
lean_dec_ref(v_pivot_1894_);
lean_dec(v_hi_1892_);
lean_dec(v_lo_1891_);
lean_dec(v_n_1890_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1902_, lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_f_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1905_, v_x_1906_, v_x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1909_, lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_f_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1909_, v_00_u03b1_1910_, v_00_u03b2_1911_, v_f_1912_, v_x_1913_, v_x_1914_);
lean_dec_ref(v_x_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_00_u03c3_1918_, lean_object* v_f_1919_, lean_object* v_as_1920_, size_t v_i_1921_, size_t v_stop_1922_, lean_object* v_b_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1919_, v_as_1920_, v_i_1921_, v_stop_1922_, v_b_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_00_u03c3_1927_, lean_object* v_f_1928_, lean_object* v_as_1929_, lean_object* v_i_1930_, lean_object* v_stop_1931_, lean_object* v_b_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; lean_object* v_res_1935_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1931_);
lean_dec(v_stop_1931_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1925_, v_00_u03b2_1926_, v_00_u03c3_1927_, v_f_1928_, v_as_1929_, v_i_boxed_1933_, v_stop_boxed_1934_, v_b_1932_);
lean_dec_ref(v_as_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_1936_, lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_f_1939_, lean_object* v_keys_1940_, lean_object* v_vals_1941_, lean_object* v_heq_1942_, lean_object* v_i_1943_, lean_object* v_acc_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1939_, v_keys_1940_, v_vals_1941_, v_i_1943_, v_acc_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_1946_, lean_object* v_00_u03b1_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_f_1949_, lean_object* v_keys_1950_, lean_object* v_vals_1951_, lean_object* v_heq_1952_, lean_object* v_i_1953_, lean_object* v_acc_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_1946_, v_00_u03b1_1947_, v_00_u03b2_1948_, v_f_1949_, v_keys_1950_, v_vals_1951_, v_heq_1952_, v_i_1953_, v_acc_1954_);
lean_dec_ref(v_vals_1951_);
lean_dec_ref(v_keys_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object* v_a_1956_, lean_object* v_x_1957_){
_start:
{
if (lean_obj_tag(v_x_1957_) == 0)
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_box(0);
return v___x_1958_;
}
else
{
lean_object* v_key_1959_; lean_object* v_value_1960_; lean_object* v_tail_1961_; uint8_t v___x_1962_; 
v_key_1959_ = lean_ctor_get(v_x_1957_, 0);
v_value_1960_ = lean_ctor_get(v_x_1957_, 1);
v_tail_1961_ = lean_ctor_get(v_x_1957_, 2);
v___x_1962_ = lean_name_eq(v_key_1959_, v_a_1956_);
if (v___x_1962_ == 0)
{
v_x_1957_ = v_tail_1961_;
goto _start;
}
else
{
lean_object* v___x_1964_; 
lean_inc(v_value_1960_);
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_value_1960_);
return v___x_1964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1965_, lean_object* v_x_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1965_, v_x_1966_);
lean_dec(v_x_1966_);
lean_dec(v_a_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_buckets_1970_; lean_object* v___x_1971_; uint64_t v___y_1973_; 
v_buckets_1970_ = lean_ctor_get(v_m_1968_, 1);
v___x_1971_ = lean_array_get_size(v_buckets_1970_);
if (lean_obj_tag(v_a_1969_) == 0)
{
uint64_t v___x_1987_; 
v___x_1987_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1973_ = v___x_1987_;
goto v___jp_1972_;
}
else
{
uint64_t v_hash_1988_; 
v_hash_1988_ = lean_ctor_get_uint64(v_a_1969_, sizeof(void*)*2);
v___y_1973_ = v_hash_1988_;
goto v___jp_1972_;
}
v___jp_1972_:
{
uint64_t v___x_1974_; uint64_t v___x_1975_; uint64_t v_fold_1976_; uint64_t v___x_1977_; uint64_t v___x_1978_; uint64_t v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; size_t v___x_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1974_ = 32ULL;
v___x_1975_ = lean_uint64_shift_right(v___y_1973_, v___x_1974_);
v_fold_1976_ = lean_uint64_xor(v___y_1973_, v___x_1975_);
v___x_1977_ = 16ULL;
v___x_1978_ = lean_uint64_shift_right(v_fold_1976_, v___x_1977_);
v___x_1979_ = lean_uint64_xor(v_fold_1976_, v___x_1978_);
v___x_1980_ = lean_uint64_to_usize(v___x_1979_);
v___x_1981_ = lean_usize_of_nat(v___x_1971_);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_sub(v___x_1981_, v___x_1982_);
v___x_1984_ = lean_usize_land(v___x_1980_, v___x_1983_);
v___x_1985_ = lean_array_uget_borrowed(v_buckets_1970_, v___x_1984_);
v___x_1986_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1969_, v___x_1985_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_m_1989_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_1992_, lean_object* v_k_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_m_1998_; lean_object* v_a_1999_; uint8_t v___x_2000_; 
v___x_1996_ = lean_nat_add(v_x_1994_, v_x_1995_);
v___x_1997_ = lean_unsigned_to_nat(1u);
v_m_1998_ = lean_nat_shiftr(v___x_1996_, v___x_1997_);
lean_dec(v___x_1996_);
v_a_1999_ = lean_array_fget_borrowed(v_as_1992_, v_m_1998_);
v___x_2000_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_1999_, v_k_1993_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; 
lean_dec(v_x_1995_);
v___x_2001_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_1993_, v_a_1999_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec(v_m_1998_);
lean_dec(v_x_1994_);
lean_inc(v_a_1999_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_a_1999_);
return v___x_2002_;
}
else
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_nat_dec_eq(v_m_1998_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = lean_nat_sub(v_m_1998_, v___x_1997_);
lean_dec(v_m_1998_);
v___x_2006_ = lean_nat_dec_lt(v___x_2005_, v_x_1994_);
if (v___x_2006_ == 0)
{
v_x_1995_ = v___x_2005_;
goto _start;
}
else
{
lean_object* v___x_2008_; 
lean_dec(v___x_2005_);
lean_dec(v_x_1994_);
v___x_2008_ = lean_box(0);
return v___x_2008_;
}
}
else
{
lean_object* v___x_2009_; 
lean_dec(v_m_1998_);
lean_dec(v_x_1994_);
v___x_2009_ = lean_box(0);
return v___x_2009_;
}
}
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
lean_dec(v_x_1994_);
v___x_2010_ = lean_nat_add(v_m_1998_, v___x_1997_);
lean_dec(v_m_1998_);
v___x_2011_ = lean_nat_dec_le(v___x_2010_, v_x_1995_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec(v___x_2010_);
lean_dec(v_x_1995_);
v___x_2012_ = lean_box(0);
return v___x_2012_;
}
else
{
v_x_1994_ = v___x_2010_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_2014_, lean_object* v_k_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2014_, v_k_2015_, v_x_2016_, v_x_2017_);
lean_dec_ref(v_k_2015_);
lean_dec_ref(v_as_2014_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2019_, lean_object* v_vals_2020_, lean_object* v_i_2021_, lean_object* v_k_2022_){
_start:
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_array_get_size(v_keys_2019_);
v___x_2024_ = lean_nat_dec_lt(v_i_2021_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_dec(v_i_2021_);
v___x_2025_ = lean_box(0);
return v___x_2025_;
}
else
{
lean_object* v_k_x27_2026_; uint8_t v___x_2027_; 
v_k_x27_2026_ = lean_array_fget_borrowed(v_keys_2019_, v_i_2021_);
v___x_2027_ = lean_name_eq(v_k_2022_, v_k_x27_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_add(v_i_2021_, v___x_2028_);
lean_dec(v_i_2021_);
v_i_2021_ = v___x_2029_;
goto _start;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_array_fget_borrowed(v_vals_2020_, v_i_2021_);
lean_dec(v_i_2021_);
lean_inc(v___x_2031_);
v___x_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2033_, lean_object* v_vals_2034_, lean_object* v_i_2035_, lean_object* v_k_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2033_, v_vals_2034_, v_i_2035_, v_k_2036_);
lean_dec(v_k_2036_);
lean_dec_ref(v_vals_2034_);
lean_dec_ref(v_keys_2033_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object* v_x_2038_, size_t v_x_2039_, lean_object* v_x_2040_){
_start:
{
if (lean_obj_tag(v_x_2038_) == 0)
{
lean_object* v_es_2041_; lean_object* v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; lean_object* v_j_2045_; lean_object* v___x_2046_; 
v_es_2041_ = lean_ctor_get(v_x_2038_, 0);
v___x_2042_ = lean_box(2);
v___x_2043_ = ((size_t)31ULL);
v___x_2044_ = lean_usize_land(v_x_2039_, v___x_2043_);
v_j_2045_ = lean_usize_to_nat(v___x_2044_);
v___x_2046_ = lean_array_get_borrowed(v___x_2042_, v_es_2041_, v_j_2045_);
lean_dec(v_j_2045_);
switch(lean_obj_tag(v___x_2046_))
{
case 0:
{
lean_object* v_key_2047_; lean_object* v_val_2048_; uint8_t v___x_2049_; 
v_key_2047_ = lean_ctor_get(v___x_2046_, 0);
v_val_2048_ = lean_ctor_get(v___x_2046_, 1);
v___x_2049_ = lean_name_eq(v_x_2040_, v_key_2047_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_box(0);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; 
lean_inc(v_val_2048_);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_val_2048_);
return v___x_2051_;
}
}
case 1:
{
lean_object* v_node_2052_; size_t v___x_2053_; size_t v___x_2054_; 
v_node_2052_ = lean_ctor_get(v___x_2046_, 0);
v___x_2053_ = ((size_t)5ULL);
v___x_2054_ = lean_usize_shift_right(v_x_2039_, v___x_2053_);
v_x_2038_ = v_node_2052_;
v_x_2039_ = v___x_2054_;
goto _start;
}
default: 
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_box(0);
return v___x_2056_;
}
}
}
else
{
lean_object* v_ks_2057_; lean_object* v_vs_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_ks_2057_ = lean_ctor_get(v_x_2038_, 0);
v_vs_2058_ = lean_ctor_get(v_x_2038_, 1);
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_2057_, v_vs_2058_, v___x_2059_, v_x_2040_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
size_t v_x_1432__boxed_2064_; lean_object* v_res_2065_; 
v_x_1432__boxed_2064_ = lean_unbox_usize(v_x_2062_);
lean_dec(v_x_2062_);
v_res_2065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2061_, v_x_1432__boxed_2064_, v_x_2063_);
lean_dec(v_x_2063_);
lean_dec_ref(v_x_2061_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
uint64_t v___y_2069_; 
if (lean_obj_tag(v_x_2067_) == 0)
{
uint64_t v___x_2072_; 
v___x_2072_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2069_ = v___x_2072_;
goto v___jp_2068_;
}
else
{
uint64_t v_hash_2073_; 
v_hash_2073_ = lean_ctor_get_uint64(v_x_2067_, sizeof(void*)*2);
v___y_2069_ = v_hash_2073_;
goto v___jp_2068_;
}
v___jp_2068_:
{
size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_uint64_to_usize(v___y_2069_);
v___x_2071_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2066_, v___x_2070_, v_x_2067_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2074_, v_x_2075_);
lean_dec(v_x_2075_);
lean_dec_ref(v_x_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object* v_declName_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v_env_2081_; lean_object* v___x_2082_; lean_object* v___x_2092_; 
v___x_2080_ = lean_st_ref_get(v_a_2078_);
v_env_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v_env_2081_);
lean_dec(v___x_2080_);
v___x_2082_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2092_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2081_, v_declName_2077_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; lean_object* v_toEnvExtension_2094_; lean_object* v_asyncMode_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_newEntries_2098_; lean_object* v___x_2099_; 
v___x_2093_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2094_ = lean_ctor_get(v___x_2093_, 0);
v_asyncMode_2095_ = lean_ctor_get(v_toEnvExtension_2094_, 2);
v___x_2096_ = lean_box(0);
lean_inc_ref(v_env_2081_);
v___x_2097_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2082_, v___x_2093_, v_env_2081_, v_asyncMode_2095_, v___x_2096_);
v_newEntries_2098_ = lean_ctor_get(v___x_2097_, 1);
lean_inc_ref(v_newEntries_2098_);
lean_dec(v___x_2097_);
v___x_2099_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_2098_, v_declName_2077_);
lean_dec_ref(v_newEntries_2098_);
if (lean_obj_tag(v___x_2099_) == 1)
{
lean_object* v___x_2100_; 
lean_dec_ref(v_env_2081_);
lean_dec(v_declName_2077_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
else
{
lean_dec(v___x_2099_);
goto v___jp_2083_;
}
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2129_; 
v_val_2101_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2103_ = v___x_2092_;
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_val_2101_);
lean_dec(v___x_2092_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2105_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v___x_2106_ = 0;
v___x_2107_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2082_, v___x_2105_, v_env_2081_, v_val_2101_, v___x_2106_);
lean_dec(v_val_2101_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_array_get_size(v___x_2107_);
v___x_2110_ = lean_nat_dec_lt(v___x_2108_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_dec_ref(v___x_2107_);
lean_del_object(v___x_2103_);
goto v___jp_2083_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_nat_sub(v___x_2109_, v___x_2111_);
v___x_2113_ = lean_nat_dec_le(v___x_2108_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec(v___x_2112_);
lean_dec_ref(v___x_2107_);
lean_del_object(v___x_2103_);
goto v___jp_2083_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0));
lean_inc(v_declName_2077_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_declName_2077_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_2107_, v___x_2115_, v___x_2108_, v___x_2112_);
lean_dec_ref_known(v___x_2115_, 2);
lean_dec_ref(v___x_2107_);
if (lean_obj_tag(v___x_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_env_2081_);
lean_dec(v_declName_2077_);
v_val_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2128_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_val_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2128_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_keys_2121_; lean_object* v___x_2123_; 
v_keys_2121_ = lean_ctor_get(v_val_2117_, 1);
lean_inc_ref(v_keys_2121_);
lean_dec(v_val_2117_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v_keys_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_keys_2121_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2123_);
v___x_2125_ = v___x_2103_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v___x_2116_);
lean_del_object(v___x_2103_);
goto v___jp_2083_;
}
}
}
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v_toEnvExtension_2085_; lean_object* v_asyncMode_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_builtin_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2084_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2085_ = lean_ctor_get(v___x_2084_, 0);
v_asyncMode_2086_ = lean_ctor_get(v_toEnvExtension_2085_, 2);
v___x_2087_ = lean_box(0);
v___x_2088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2082_, v___x_2084_, v_env_2081_, v_asyncMode_2086_, v___x_2087_);
v_builtin_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc_ref(v_builtin_2089_);
lean_dec(v___x_2088_);
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_2089_, v_declName_2077_);
lean_dec(v_declName_2077_);
lean_dec_ref(v_builtin_2089_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2130_, v_a_2131_);
lean_dec(v_a_2131_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object* v_declName_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2134_, v_a_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object* v_declName_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_2144_, lean_object* v_m_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2145_, v_a_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_2148_, lean_object* v_m_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_2148_, v_m_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_m_2149_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2153_, v_x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_2156_, v_x_2157_, v_x_2158_);
lean_dec(v_x_2158_);
lean_dec_ref(v_x_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object* v_as_2160_, lean_object* v_k_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2160_, v_k_2161_, v_x_2162_, v_x_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_2166_, lean_object* v_k_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(v_as_2166_, v_k_2167_, v_x_2168_, v_x_2169_, v_x_2170_);
lean_dec_ref(v_k_2167_);
lean_dec_ref(v_as_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2172_, lean_object* v_a_2173_, lean_object* v_x_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2173_, v_x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_a_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_2176_, v_a_2177_, v_x_2178_);
lean_dec(v_x_2178_);
lean_dec(v_a_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2180_, lean_object* v_x_2181_, size_t v_x_2182_, lean_object* v_x_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2181_, v_x_2182_, v_x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
size_t v_x_1619__boxed_2189_; lean_object* v_res_2190_; 
v_x_1619__boxed_2189_ = lean_unbox_usize(v_x_2187_);
lean_dec(v_x_2187_);
v_res_2190_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_2185_, v_x_2186_, v_x_1619__boxed_2189_, v_x_2188_);
lean_dec(v_x_2188_);
lean_dec_ref(v_x_2186_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2191_, lean_object* v_keys_2192_, lean_object* v_vals_2193_, lean_object* v_heq_2194_, lean_object* v_i_2195_, lean_object* v_k_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2192_, v_vals_2193_, v_i_2195_, v_k_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2198_, lean_object* v_keys_2199_, lean_object* v_vals_2200_, lean_object* v_heq_2201_, lean_object* v_i_2202_, lean_object* v_k_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_2198_, v_keys_2199_, v_vals_2200_, v_heq_2201_, v_i_2202_, v_k_2203_);
lean_dec(v_k_2203_);
lean_dec_ref(v_vals_2200_);
lean_dec_ref(v_keys_2199_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object* v_declName_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___x_2208_; lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2223_; 
v___x_2208_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2205_, v_a_2206_);
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2223_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2223_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
if (lean_obj_tag(v_a_2209_) == 0)
{
uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2213_ = 0;
v___x_2214_ = lean_box(v___x_2213_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2214_);
v___x_2216_ = v___x_2211_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
else
{
uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
lean_dec_ref_known(v_a_2209_, 1);
v___x_2218_ = 1;
v___x_2219_ = lean_box(v___x_2218_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2219_);
v___x_2221_ = v___x_2211_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object* v_declName_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2224_, v_a_2225_);
lean_dec(v_a_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object* v_declName_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2228_, v_a_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object* v_declName_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object* v_declName_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v_env_2242_; lean_object* v___x_2243_; lean_object* v_toEnvExtension_2244_; lean_object* v_asyncMode_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_builtin_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2241_ = lean_st_ref_get(v_a_2239_);
v_env_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc_ref(v_env_2242_);
lean_dec(v___x_2241_);
v___x_2243_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2244_ = lean_ctor_get(v___x_2243_, 0);
v_asyncMode_2245_ = lean_ctor_get(v_toEnvExtension_2244_, 2);
v___x_2246_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2247_ = lean_box(0);
v___x_2248_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2246_, v___x_2243_, v_env_2242_, v_asyncMode_2245_, v___x_2247_);
v_builtin_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_ref(v_builtin_2249_);
lean_dec(v___x_2248_);
v___x_2250_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_2249_, v_declName_2238_);
lean_dec_ref(v_builtin_2249_);
v___x_2251_ = lean_box(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object* v_declName_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec(v_declName_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object* v_declName_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2257_, v_a_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object* v_declName_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_declName_2262_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object* v_declName_2267_, lean_object* v_keys_2268_, lean_object* v_s_2269_){
_start:
{
lean_object* v_builtin_2270_; lean_object* v_newEntries_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2279_; 
v_builtin_2270_ = lean_ctor_get(v_s_2269_, 0);
v_newEntries_2271_ = lean_ctor_get(v_s_2269_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_s_2269_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2273_ = v_s_2269_;
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_newEntries_2271_);
lean_inc(v_builtin_2270_);
lean_dec(v_s_2269_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_2271_, v_declName_2267_, v_keys_2268_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v___x_2275_);
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_builtin_2270_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2280_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
lean_ctor_set(v___x_2285_, 2, v___x_2284_);
lean_ctor_set(v___x_2285_, 3, v___x_2284_);
lean_ctor_set(v___x_2285_, 4, v___x_2283_);
lean_ctor_set(v___x_2285_, 5, v___x_2283_);
lean_ctor_set(v___x_2285_, 6, v___x_2283_);
lean_ctor_set(v___x_2285_, 7, v___x_2283_);
lean_ctor_set(v___x_2285_, 8, v___x_2283_);
lean_ctor_set(v___x_2285_, 9, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_unsigned_to_nat(32u);
v___x_2287_ = lean_mk_empty_array_with_capacity(v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2289_ = ((size_t)5ULL);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_unsigned_to_nat(32u);
v___x_2292_ = lean_mk_empty_array_with_capacity(v___x_2291_);
v___x_2293_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
v___x_2294_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2292_);
lean_ctor_set(v___x_2294_, 2, v___x_2290_);
lean_ctor_set(v___x_2294_, 3, v___x_2290_);
lean_ctor_set_usize(v___x_2294_, 4, v___x_2289_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = lean_box(1);
v___x_2296_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
v___x_2297_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2296_);
lean_ctor_set(v___x_2298_, 2, v___x_2295_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object* v_msgData_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v_env_2304_; lean_object* v_options_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2303_ = lean_st_ref_get(v___y_2301_);
v_env_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc_ref(v_env_2304_);
lean_dec(v___x_2303_);
v_options_2305_ = lean_ctor_get(v___y_2300_, 2);
v___x_2306_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2307_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2305_);
v___x_2308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2308_, 0, v_env_2304_);
lean_ctor_set(v___x_2308_, 1, v___x_2306_);
lean_ctor_set(v___x_2308_, 2, v___x_2307_);
lean_ctor_set(v___x_2308_, 3, v_options_2305_);
v___x_2309_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v_msgData_2299_);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object* v_msg_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_ref_2320_; lean_object* v___x_2321_; lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2330_; 
v_ref_2320_ = lean_ctor_get(v___y_2317_, 5);
v___x_2321_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_2316_, v___y_2317_, v___y_2318_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_inc(v_ref_2320_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_ref_2320_);
lean_ctor_set(v___x_2326_, 1, v_a_2322_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set_tag(v___x_2324_, 1);
lean_ctor_set(v___x_2324_, 0, v___x_2326_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object* v_msg_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2335_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0(void){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3));
v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object* v_declName_2349_, lean_object* v_keys_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v_env_2355_; lean_object* v___f_2356_; lean_object* v___y_2358_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___x_2406_; 
v___x_2354_ = lean_st_ref_get(v_a_2352_);
v_env_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc_ref(v_env_2355_);
lean_dec(v___x_2354_);
lean_inc(v_declName_2349_);
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0), 3, 2);
lean_closure_set(v___f_2356_, 0, v_declName_2349_);
lean_closure_set(v___f_2356_, 1, v_keys_2350_);
v___x_2406_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2355_, v_declName_2349_);
lean_dec_ref(v_env_2355_);
if (lean_obj_tag(v___x_2406_) == 0)
{
v___y_2386_ = v_a_2351_;
v___y_2387_ = v_a_2352_;
goto v___jp_2385_;
}
else
{
uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref_known(v___x_2406_, 1);
lean_dec_ref(v___f_2356_);
v___x_2407_ = 0;
v___x_2408_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2409_ = l_Lean_MessageData_ofConstName(v_declName_2349_, v___x_2407_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2412_, v_a_2351_, v_a_2352_);
return v___x_2413_;
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v_env_2360_; lean_object* v_nextMacroScope_2361_; lean_object* v_ngen_2362_; lean_object* v_auxDeclNGen_2363_; lean_object* v_traceState_2364_; lean_object* v_messages_2365_; lean_object* v_infoState_2366_; lean_object* v_snapshotTasks_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2383_; 
v___x_2359_ = lean_st_ref_take(v___y_2358_);
v_env_2360_ = lean_ctor_get(v___x_2359_, 0);
v_nextMacroScope_2361_ = lean_ctor_get(v___x_2359_, 1);
v_ngen_2362_ = lean_ctor_get(v___x_2359_, 2);
v_auxDeclNGen_2363_ = lean_ctor_get(v___x_2359_, 3);
v_traceState_2364_ = lean_ctor_get(v___x_2359_, 4);
v_messages_2365_ = lean_ctor_get(v___x_2359_, 6);
v_infoState_2366_ = lean_ctor_get(v___x_2359_, 7);
v_snapshotTasks_2367_ = lean_ctor_get(v___x_2359_, 8);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v___x_2359_, 5);
lean_dec(v_unused_2384_);
v___x_2369_ = v___x_2359_;
v_isShared_2370_ = v_isSharedCheck_2383_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_snapshotTasks_2367_);
lean_inc(v_infoState_2366_);
lean_inc(v_messages_2365_);
lean_inc(v_traceState_2364_);
lean_inc(v_auxDeclNGen_2363_);
lean_inc(v_ngen_2362_);
lean_inc(v_nextMacroScope_2361_);
lean_inc(v_env_2360_);
lean_dec(v___x_2359_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2383_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v_toEnvExtension_2372_; lean_object* v_asyncMode_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2371_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2372_ = lean_ctor_get(v___x_2371_, 0);
v_asyncMode_2373_ = lean_ctor_get(v_toEnvExtension_2372_, 2);
v___x_2374_ = lean_box(0);
v___x_2375_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2371_, v_env_2360_, v___f_2356_, v_asyncMode_2373_, v___x_2374_);
v___x_2376_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 5, v___x_2376_);
lean_ctor_set(v___x_2369_, 0, v___x_2375_);
v___x_2378_ = v___x_2369_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_nextMacroScope_2361_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_ngen_2362_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_auxDeclNGen_2363_);
lean_ctor_set(v_reuseFailAlloc_2382_, 4, v_traceState_2364_);
lean_ctor_set(v_reuseFailAlloc_2382_, 5, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2382_, 6, v_messages_2365_);
lean_ctor_set(v_reuseFailAlloc_2382_, 7, v_infoState_2366_);
lean_ctor_set(v_reuseFailAlloc_2382_, 8, v_snapshotTasks_2367_);
v___x_2378_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = lean_st_ref_set(v___y_2358_, v___x_2378_);
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
}
v___jp_2385_:
{
lean_object* v___x_2388_; 
lean_inc(v_declName_2349_);
v___x_2388_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2349_, v___y_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; uint8_t v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
if (v___x_2390_ == 0)
{
lean_dec(v_declName_2349_);
v___y_2358_ = v___y_2387_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v___f_2356_);
v___x_2391_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2392_ = 0;
v___x_2393_ = l_Lean_MessageData_ofConstName(v_declName_2349_, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2391_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2396_, v___y_2386_, v___y_2387_);
return v___x_2397_;
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v___f_2356_);
lean_dec(v_declName_2349_);
v_a_2398_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2388_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2388_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object* v_declName_2414_, lean_object* v_keys_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2414_, v_keys_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object* v_00_u03b1_2420_, lean_object* v_msg_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2421_, v___y_2422_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(v_00_u03b1_2426_, v_msg_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_2432_){
_start:
{
if (lean_obj_tag(v_e_2432_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
v_a_2434_ = lean_ctor_get(v_e_2432_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_e_2432_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v_e_2432_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v_e_2432_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_mk_io_user_error(v_a_2434_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set_tag(v___x_2436_, 1);
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v_e_2432_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_e_2432_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v_e_2432_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v_e_2432_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 0);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_2454_, lean_object* v_e_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_e_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(v_00_u03b1_2458_, v_e_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object* v_declName_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_env_2472_; lean_object* v_opts_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; 
v_env_2472_ = lean_ctor_get(v_a_2470_, 0);
v_opts_2473_ = lean_ctor_get(v_a_2470_, 1);
v___x_2474_ = 0;
lean_inc(v_declName_2469_);
lean_inc_ref(v_env_2472_);
v___x_2475_ = l_Lean_Environment_find_x3f(v_env_2472_, v_declName_2469_, v___x_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2476_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0));
v___x_2477_ = 1;
v___x_2478_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2469_, v___x_2477_);
v___x_2479_ = lean_string_append(v___x_2476_, v___x_2478_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2481_ = lean_string_append(v___x_2479_, v___x_2480_);
v___x_2482_ = lean_mk_io_user_error(v___x_2481_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
else
{
lean_object* v_val_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2529_; 
v_val_2484_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2486_ = v___x_2475_;
v_isShared_2487_ = v_isSharedCheck_2529_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_val_2484_);
lean_dec(v___x_2475_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2529_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_ConstantInfo_type(v_val_2484_);
if (lean_obj_tag(v___x_2505_) == 4)
{
lean_object* v_declName_2506_; 
v_declName_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_declName_2506_);
lean_dec_ref_known(v___x_2505_, 2);
if (lean_obj_tag(v_declName_2506_) == 1)
{
lean_object* v_pre_2507_; 
v_pre_2507_ = lean_ctor_get(v_declName_2506_, 0);
lean_inc(v_pre_2507_);
if (lean_obj_tag(v_pre_2507_) == 1)
{
lean_object* v_pre_2508_; 
v_pre_2508_ = lean_ctor_get(v_pre_2507_, 0);
lean_inc(v_pre_2508_);
if (lean_obj_tag(v_pre_2508_) == 1)
{
lean_object* v_pre_2509_; 
v_pre_2509_ = lean_ctor_get(v_pre_2508_, 0);
lean_inc(v_pre_2509_);
if (lean_obj_tag(v_pre_2509_) == 1)
{
lean_object* v_pre_2510_; 
v_pre_2510_ = lean_ctor_get(v_pre_2509_, 0);
lean_inc(v_pre_2510_);
if (lean_obj_tag(v_pre_2510_) == 1)
{
lean_object* v_pre_2511_; 
v_pre_2511_ = lean_ctor_get(v_pre_2510_, 0);
if (lean_obj_tag(v_pre_2511_) == 0)
{
lean_object* v_str_2512_; lean_object* v_str_2513_; lean_object* v_str_2514_; lean_object* v_str_2515_; lean_object* v_str_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_str_2512_ = lean_ctor_get(v_declName_2506_, 1);
lean_inc_ref(v_str_2512_);
lean_dec_ref_known(v_declName_2506_, 2);
v_str_2513_ = lean_ctor_get(v_pre_2507_, 1);
lean_inc_ref(v_str_2513_);
lean_dec_ref_known(v_pre_2507_, 2);
v_str_2514_ = lean_ctor_get(v_pre_2508_, 1);
lean_inc_ref(v_str_2514_);
lean_dec_ref_known(v_pre_2508_, 2);
v_str_2515_ = lean_ctor_get(v_pre_2509_, 1);
lean_inc_ref(v_str_2515_);
lean_dec_ref_known(v_pre_2509_, 2);
v_str_2516_ = lean_ctor_get(v_pre_2510_, 1);
lean_inc_ref(v_str_2516_);
lean_dec_ref_known(v_pre_2510_, 2);
v___x_2517_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0));
v___x_2518_ = lean_string_dec_eq(v_str_2516_, v___x_2517_);
lean_dec_ref(v_str_2516_);
if (v___x_2518_ == 0)
{
lean_dec_ref(v_str_2515_);
lean_dec_ref(v_str_2514_);
lean_dec_ref(v_str_2513_);
lean_dec_ref(v_str_2512_);
goto v___jp_2488_;
}
else
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1));
v___x_2520_ = lean_string_dec_eq(v_str_2515_, v___x_2519_);
lean_dec_ref(v_str_2515_);
if (v___x_2520_ == 0)
{
lean_dec_ref(v_str_2514_);
lean_dec_ref(v_str_2513_);
lean_dec_ref(v_str_2512_);
goto v___jp_2488_;
}
else
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4));
v___x_2522_ = lean_string_dec_eq(v_str_2514_, v___x_2521_);
lean_dec_ref(v_str_2514_);
if (v___x_2522_ == 0)
{
lean_dec_ref(v_str_2513_);
lean_dec_ref(v_str_2512_);
goto v___jp_2488_;
}
else
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5));
v___x_2524_ = lean_string_dec_eq(v_str_2513_, v___x_2523_);
lean_dec_ref(v_str_2513_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v_str_2512_);
goto v___jp_2488_;
}
else
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6));
v___x_2526_ = lean_string_dec_eq(v_str_2512_, v___x_2525_);
lean_dec_ref(v_str_2512_);
if (v___x_2526_ == 0)
{
goto v___jp_2488_;
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_del_object(v___x_2486_);
lean_dec(v_val_2484_);
v___x_2527_ = l_Lean_Environment_evalConst___redArg(v_env_2472_, v_opts_2473_, v_declName_2469_, v___x_2526_);
lean_dec(v_declName_2469_);
v___x_2528_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_2527_);
return v___x_2528_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2510_, 2);
lean_dec_ref_known(v_pre_2509_, 2);
lean_dec_ref_known(v_pre_2508_, 2);
lean_dec_ref_known(v_pre_2507_, 2);
lean_dec_ref_known(v_declName_2506_, 2);
goto v___jp_2488_;
}
}
else
{
lean_dec(v_pre_2510_);
lean_dec_ref_known(v_pre_2509_, 2);
lean_dec_ref_known(v_pre_2508_, 2);
lean_dec_ref_known(v_pre_2507_, 2);
lean_dec_ref_known(v_declName_2506_, 2);
goto v___jp_2488_;
}
}
else
{
lean_dec(v_pre_2509_);
lean_dec_ref_known(v_pre_2508_, 2);
lean_dec_ref_known(v_pre_2507_, 2);
lean_dec_ref_known(v_declName_2506_, 2);
goto v___jp_2488_;
}
}
else
{
lean_dec(v_pre_2508_);
lean_dec_ref_known(v_pre_2507_, 2);
lean_dec_ref_known(v_declName_2506_, 2);
goto v___jp_2488_;
}
}
else
{
lean_dec_ref_known(v_declName_2506_, 2);
lean_dec(v_pre_2507_);
goto v___jp_2488_;
}
}
else
{
lean_dec(v_declName_2506_);
goto v___jp_2488_;
}
}
else
{
lean_dec_ref(v___x_2505_);
goto v___jp_2488_;
}
v___jp_2488_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2489_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2));
v___x_2490_ = l_Lean_privateToUserName(v_declName_2469_);
v___x_2491_ = 1;
v___x_2492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2490_, v___x_2491_);
v___x_2493_ = lean_string_append(v___x_2489_, v___x_2492_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3));
v___x_2495_ = lean_string_append(v___x_2493_, v___x_2494_);
v___x_2496_ = l_Lean_ConstantInfo_type(v_val_2484_);
lean_dec(v_val_2484_);
v___x_2497_ = lean_expr_dbg_to_string(v___x_2496_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = lean_string_append(v___x_2495_, v___x_2497_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2500_ = lean_string_append(v___x_2498_, v___x_2499_);
v___x_2501_ = lean_mk_io_user_error(v___x_2500_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2501_);
v___x_2503_ = v___x_2486_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object* v_declName_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2530_, v_a_2531_);
lean_dec_ref(v_a_2531_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object* v_e_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_declName_2537_; lean_object* v___x_2538_; 
v_declName_2537_ = lean_ctor_get(v_e_2534_, 0);
lean_inc(v_declName_2537_);
v___x_2538_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2537_, v_a_2535_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2547_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2547_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_e_2534_);
lean_ctor_set(v___x_2543_, 1, v_a_2539_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref(v_e_2534_);
v_a_2548_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2538_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2538_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object* v_e_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2556_, v_a_2557_);
lean_dec_ref(v_a_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
v___x_2562_ = lean_st_mk_ref(v___x_2561_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___y_2566_){
_start:
{
lean_inc_ref(v___y_2566_);
return v___y_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_2567_);
lean_dec_ref(v___y_2567_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2574_, v___y_2575_, v___y_2576_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v_x_2574_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_e_2579_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2580_; 
v_toCbvSimprocOLeanEntry_2580_ = lean_ctor_get(v_e_2579_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2580_);
return v_toCbvSimprocOLeanEntry_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_e_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_2581_);
lean_dec_ref(v_e_2581_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_s_2583_, lean_object* v_e_2584_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2585_; lean_object* v_proc_2586_; lean_object* v_declName_2587_; uint8_t v_phase_2588_; lean_object* v_keys_2589_; lean_object* v___x_2590_; 
v_toCbvSimprocOLeanEntry_2585_ = lean_ctor_get(v_e_2584_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2585_);
v_proc_2586_ = lean_ctor_get(v_e_2584_, 1);
lean_inc_ref(v_proc_2586_);
lean_dec_ref(v_e_2584_);
v_declName_2587_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2585_, 0);
lean_inc(v_declName_2587_);
v_phase_2588_ = lean_ctor_get_uint8(v_toCbvSimprocOLeanEntry_2585_, sizeof(void*)*2);
v_keys_2589_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2585_, 1);
lean_inc_ref(v_keys_2589_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_2585_);
v___x_2590_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_2583_, v_keys_2589_, v_declName_2587_, v_phase_2588_, v_proc_2586_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_a_2592_);
lean_inc_ref_n(v___x_2593_, 2);
v___x_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2595_, v_a_2596_);
lean_dec_ref(v_x_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___x_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_st_ref_get(v___x_2598_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___x_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2602_);
lean_dec(v___x_2602_);
return v_res_2604_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___f_2614_; 
v___x_2613_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___f_2614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2614_, 0, v___x_2613_);
return v___f_2614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___f_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___x_2622_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___f_2620_);
lean_ctor_set(v___x_2622_, 2, v___f_2619_);
lean_ctor_set(v___x_2622_, 3, v___f_2618_);
lean_ctor_set(v___x_2622_, 4, v___f_2617_);
lean_ctor_set(v___x_2622_, 5, v___f_2616_);
lean_ctor_set(v___x_2622_, 6, v___f_2615_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2625_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_a_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object* v_declName_2628_, lean_object* v_s_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_2629_, v_declName_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2631_, lean_object* v_i_2632_, lean_object* v_k_2633_){
_start:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_array_get_size(v_keys_2631_);
v___x_2635_ = lean_nat_dec_lt(v_i_2632_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_dec(v_i_2632_);
return v___x_2635_;
}
else
{
lean_object* v_k_x27_2636_; uint8_t v___x_2637_; 
v_k_x27_2636_ = lean_array_fget_borrowed(v_keys_2631_, v_i_2632_);
v___x_2637_ = lean_name_eq(v_k_2633_, v_k_x27_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_unsigned_to_nat(1u);
v___x_2639_ = lean_nat_add(v_i_2632_, v___x_2638_);
lean_dec(v_i_2632_);
v_i_2632_ = v___x_2639_;
goto _start;
}
else
{
lean_dec(v_i_2632_);
return v___x_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2641_, lean_object* v_i_2642_, lean_object* v_k_2643_){
_start:
{
uint8_t v_res_2644_; lean_object* v_r_2645_; 
v_res_2644_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2641_, v_i_2642_, v_k_2643_);
lean_dec(v_k_2643_);
lean_dec_ref(v_keys_2641_);
v_r_2645_ = lean_box(v_res_2644_);
return v_r_2645_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_2646_, size_t v_x_2647_, lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2646_) == 0)
{
lean_object* v_es_2649_; lean_object* v___x_2650_; size_t v___x_2651_; size_t v___x_2652_; lean_object* v_j_2653_; lean_object* v___x_2654_; 
v_es_2649_ = lean_ctor_get(v_x_2646_, 0);
v___x_2650_ = lean_box(2);
v___x_2651_ = ((size_t)31ULL);
v___x_2652_ = lean_usize_land(v_x_2647_, v___x_2651_);
v_j_2653_ = lean_usize_to_nat(v___x_2652_);
v___x_2654_ = lean_array_get_borrowed(v___x_2650_, v_es_2649_, v_j_2653_);
lean_dec(v_j_2653_);
switch(lean_obj_tag(v___x_2654_))
{
case 0:
{
lean_object* v_key_2655_; uint8_t v___x_2656_; 
v_key_2655_ = lean_ctor_get(v___x_2654_, 0);
v___x_2656_ = lean_name_eq(v_x_2648_, v_key_2655_);
return v___x_2656_;
}
case 1:
{
lean_object* v_node_2657_; size_t v___x_2658_; size_t v___x_2659_; 
v_node_2657_ = lean_ctor_get(v___x_2654_, 0);
v___x_2658_ = ((size_t)5ULL);
v___x_2659_ = lean_usize_shift_right(v_x_2647_, v___x_2658_);
v_x_2646_ = v_node_2657_;
v_x_2647_ = v___x_2659_;
goto _start;
}
default: 
{
uint8_t v___x_2661_; 
v___x_2661_ = 0;
return v___x_2661_;
}
}
}
else
{
lean_object* v_ks_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v_ks_2662_ = lean_ctor_get(v_x_2646_, 0);
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_2662_, v___x_2663_, v_x_2648_);
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_){
_start:
{
size_t v_x_547__boxed_2668_; uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_x_547__boxed_2668_ = lean_unbox_usize(v_x_2666_);
lean_dec(v_x_2666_);
v_res_2669_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2665_, v_x_547__boxed_2668_, v_x_2667_);
lean_dec(v_x_2667_);
lean_dec_ref(v_x_2665_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object* v_x_2671_, lean_object* v_x_2672_){
_start:
{
uint64_t v___y_2674_; 
if (lean_obj_tag(v_x_2672_) == 0)
{
uint64_t v___x_2677_; 
v___x_2677_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2674_ = v___x_2677_;
goto v___jp_2673_;
}
else
{
uint64_t v_hash_2678_; 
v_hash_2678_ = lean_ctor_get_uint64(v_x_2672_, sizeof(void*)*2);
v___y_2674_ = v_hash_2678_;
goto v___jp_2673_;
}
v___jp_2673_:
{
size_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = lean_uint64_to_usize(v___y_2674_);
v___x_2676_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2671_, v___x_2675_, v_x_2672_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
uint8_t v_res_2681_; lean_object* v_r_2682_; 
v_res_2681_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2679_, v_x_2680_);
lean_dec(v_x_2680_);
lean_dec_ref(v_x_2679_);
v_r_2682_ = lean_box(v_res_2681_);
return v_r_2682_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2684_ = l_Lean_stringToMessageData(v___x_2683_);
return v___x_2684_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1));
v___x_2687_ = l_Lean_stringToMessageData(v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object* v_declName_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; lean_object* v_env_2693_; lean_object* v___x_2694_; lean_object* v_ext_2695_; lean_object* v_toEnvExtension_2696_; lean_object* v_asyncMode_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v_simprocNames_2700_; lean_object* v___f_2701_; lean_object* v___y_2703_; uint8_t v___x_2726_; 
v___x_2692_ = lean_st_ref_get(v_a_2690_);
v_env_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc_ref(v_env_2693_);
lean_dec(v___x_2692_);
v___x_2694_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_2695_ = lean_ctor_get(v___x_2694_, 1);
v_toEnvExtension_2696_ = lean_ctor_get(v_ext_2695_, 0);
v_asyncMode_2697_ = lean_ctor_get(v_toEnvExtension_2696_, 2);
v___x_2698_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_2699_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2698_, v___x_2694_, v_env_2693_, v_asyncMode_2697_);
v_simprocNames_2700_ = lean_ctor_get(v___x_2699_, 3);
lean_inc_ref(v_simprocNames_2700_);
lean_dec(v___x_2699_);
lean_inc(v_declName_2688_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_2701_, 0, v_declName_2688_);
v___x_2726_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_2700_, v_declName_2688_);
lean_dec_ref(v_simprocNames_2700_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec_ref(v___f_2701_);
v___x_2727_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0);
v___x_2728_ = l_Lean_MessageData_ofConstName(v_declName_2688_, v___x_2726_);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2731_, v_a_2689_, v_a_2690_);
return v___x_2732_;
}
else
{
lean_dec(v_declName_2688_);
v___y_2703_ = v_a_2690_;
goto v___jp_2702_;
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v_env_2705_; lean_object* v_nextMacroScope_2706_; lean_object* v_ngen_2707_; lean_object* v_auxDeclNGen_2708_; lean_object* v_traceState_2709_; lean_object* v_messages_2710_; lean_object* v_infoState_2711_; lean_object* v_snapshotTasks_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2724_; 
v___x_2704_ = lean_st_ref_take(v___y_2703_);
v_env_2705_ = lean_ctor_get(v___x_2704_, 0);
v_nextMacroScope_2706_ = lean_ctor_get(v___x_2704_, 1);
v_ngen_2707_ = lean_ctor_get(v___x_2704_, 2);
v_auxDeclNGen_2708_ = lean_ctor_get(v___x_2704_, 3);
v_traceState_2709_ = lean_ctor_get(v___x_2704_, 4);
v_messages_2710_ = lean_ctor_get(v___x_2704_, 6);
v_infoState_2711_ = lean_ctor_get(v___x_2704_, 7);
v_snapshotTasks_2712_ = lean_ctor_get(v___x_2704_, 8);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; 
v_unused_2725_ = lean_ctor_get(v___x_2704_, 5);
lean_dec(v_unused_2725_);
v___x_2714_ = v___x_2704_;
v_isShared_2715_ = v_isSharedCheck_2724_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_snapshotTasks_2712_);
lean_inc(v_infoState_2711_);
lean_inc(v_messages_2710_);
lean_inc(v_traceState_2709_);
lean_inc(v_auxDeclNGen_2708_);
lean_inc(v_ngen_2707_);
lean_inc(v_nextMacroScope_2706_);
lean_inc(v_env_2705_);
lean_dec(v___x_2704_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2724_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2694_, v_env_2705_, v___f_2701_);
v___x_2717_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 5, v___x_2717_);
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_nextMacroScope_2706_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_ngen_2707_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_auxDeclNGen_2708_);
lean_ctor_set(v_reuseFailAlloc_2723_, 4, v_traceState_2709_);
lean_ctor_set(v_reuseFailAlloc_2723_, 5, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2723_, 6, v_messages_2710_);
lean_ctor_set(v_reuseFailAlloc_2723_, 7, v_infoState_2711_);
lean_ctor_set(v_reuseFailAlloc_2723_, 8, v_snapshotTasks_2712_);
v___x_2719_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_st_ref_set(v___y_2703_, v___x_2719_);
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object* v_declName_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2733_, v_a_2734_, v_a_2735_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object* v_00_u03b2_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2739_, v_x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
uint8_t v_res_2745_; lean_object* v_r_2746_; 
v_res_2745_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(v_00_u03b2_2742_, v_x_2743_, v_x_2744_);
lean_dec(v_x_2744_);
lean_dec_ref(v_x_2743_);
v_r_2746_ = lean_box(v_res_2745_);
return v_r_2746_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_2747_, lean_object* v_x_2748_, size_t v_x_2749_, lean_object* v_x_2750_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2748_, v_x_2749_, v_x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
size_t v_x_698__boxed_2756_; uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_x_698__boxed_2756_ = lean_unbox_usize(v_x_2754_);
lean_dec(v_x_2754_);
v_res_2757_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_2752_, v_x_2753_, v_x_698__boxed_2756_, v_x_2755_);
lean_dec(v_x_2755_);
lean_dec_ref(v_x_2753_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2759_, lean_object* v_keys_2760_, lean_object* v_vals_2761_, lean_object* v_heq_2762_, lean_object* v_i_2763_, lean_object* v_k_2764_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2760_, v_i_2763_, v_k_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2766_, lean_object* v_keys_2767_, lean_object* v_vals_2768_, lean_object* v_heq_2769_, lean_object* v_i_2770_, lean_object* v_k_2771_){
_start:
{
uint8_t v_res_2772_; lean_object* v_r_2773_; 
v_res_2772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_2766_, v_keys_2767_, v_vals_2768_, v_heq_2769_, v_i_2770_, v_k_2771_);
lean_dec(v_k_2771_);
lean_dec_ref(v_vals_2768_);
lean_dec_ref(v_keys_2767_);
v_r_2773_ = lean_box(v_res_2772_);
return v_r_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object* v_ext_2774_, lean_object* v_b_2775_, uint8_t v_kind_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_currNamespace_2780_; lean_object* v___x_2781_; lean_object* v_env_2782_; lean_object* v_nextMacroScope_2783_; lean_object* v_ngen_2784_; lean_object* v_auxDeclNGen_2785_; lean_object* v_traceState_2786_; lean_object* v_messages_2787_; lean_object* v_infoState_2788_; lean_object* v_snapshotTasks_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2801_; 
v_currNamespace_2780_ = lean_ctor_get(v___y_2777_, 6);
v___x_2781_ = lean_st_ref_take(v___y_2778_);
v_env_2782_ = lean_ctor_get(v___x_2781_, 0);
v_nextMacroScope_2783_ = lean_ctor_get(v___x_2781_, 1);
v_ngen_2784_ = lean_ctor_get(v___x_2781_, 2);
v_auxDeclNGen_2785_ = lean_ctor_get(v___x_2781_, 3);
v_traceState_2786_ = lean_ctor_get(v___x_2781_, 4);
v_messages_2787_ = lean_ctor_get(v___x_2781_, 6);
v_infoState_2788_ = lean_ctor_get(v___x_2781_, 7);
v_snapshotTasks_2789_ = lean_ctor_get(v___x_2781_, 8);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v___x_2781_, 5);
lean_dec(v_unused_2802_);
v___x_2791_ = v___x_2781_;
v_isShared_2792_ = v_isSharedCheck_2801_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_snapshotTasks_2789_);
lean_inc(v_infoState_2788_);
lean_inc(v_messages_2787_);
lean_inc(v_traceState_2786_);
lean_inc(v_auxDeclNGen_2785_);
lean_inc(v_ngen_2784_);
lean_inc(v_nextMacroScope_2783_);
lean_inc(v_env_2782_);
lean_dec(v___x_2781_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2801_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_inc(v_currNamespace_2780_);
v___x_2793_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2782_, v_ext_2774_, v_b_2775_, v_kind_2776_, v_currNamespace_2780_);
v___x_2794_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 5, v___x_2794_);
lean_ctor_set(v___x_2791_, 0, v___x_2793_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_nextMacroScope_2783_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_ngen_2784_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_auxDeclNGen_2785_);
lean_ctor_set(v_reuseFailAlloc_2800_, 4, v_traceState_2786_);
lean_ctor_set(v_reuseFailAlloc_2800_, 5, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2800_, 6, v_messages_2787_);
lean_ctor_set(v_reuseFailAlloc_2800_, 7, v_infoState_2788_);
lean_ctor_set(v_reuseFailAlloc_2800_, 8, v_snapshotTasks_2789_);
v___x_2796_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_st_ref_set(v___y_2778_, v___x_2796_);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_2803_, lean_object* v_b_2804_, lean_object* v_kind_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v_kind_boxed_2809_; lean_object* v_res_2810_; 
v_kind_boxed_2809_ = lean_unbox(v_kind_2805_);
v_res_2810_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2803_, v_b_2804_, v_kind_boxed_2809_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object* v_00_u03b1_2811_, lean_object* v_00_u03b2_2812_, lean_object* v_00_u03c3_2813_, lean_object* v_ext_2814_, lean_object* v_b_2815_, uint8_t v_kind_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2814_, v_b_2815_, v_kind_2816_, v___y_2817_, v___y_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_00_u03b2_2822_, lean_object* v_00_u03c3_2823_, lean_object* v_ext_2824_, lean_object* v_b_2825_, lean_object* v_kind_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_kind_boxed_2830_; lean_object* v_res_2831_; 
v_kind_boxed_2830_ = lean_unbox(v_kind_2826_);
v_res_2831_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(v_00_u03b1_2821_, v_00_u03b2_2822_, v_00_u03c3_2823_, v_ext_2824_, v_b_2825_, v_kind_boxed_2830_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
return v_res_2831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0));
v___x_2834_ = l_Lean_stringToMessageData(v___x_2833_);
return v___x_2834_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2));
v___x_2837_ = l_Lean_stringToMessageData(v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object* v_declName_2838_, uint8_t v_kind_2839_, uint8_t v_phase_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2844_; lean_object* v_env_2845_; lean_object* v_options_2846_; lean_object* v_ref_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2844_ = lean_st_ref_get(v_a_2842_);
v_env_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_ref(v_env_2845_);
lean_dec(v___x_2844_);
v_options_2846_ = lean_ctor_get(v_a_2841_, 2);
v_ref_2847_ = lean_ctor_get(v_a_2841_, 5);
lean_inc_ref(v_options_2846_);
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v_env_2845_);
lean_ctor_set(v___x_2848_, 1, v_options_2846_);
lean_inc(v_declName_2838_);
v___x_2849_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2838_, v___x_2848_);
lean_dec_ref_known(v___x_2848_, 2);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v_a_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
lean_inc(v_declName_2838_);
v___x_2851_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2838_, v_a_2842_);
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
if (lean_obj_tag(v_a_2852_) == 1)
{
lean_object* v_val_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_val_2853_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_val_2853_);
lean_dec_ref_known(v_a_2852_, 1);
v___x_2854_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v___x_2855_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2855_, 0, v_declName_2838_);
lean_ctor_set(v___x_2855_, 1, v_val_2853_);
lean_ctor_set_uint8(v___x_2855_, sizeof(void*)*2, v_phase_2840_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v_a_2850_);
v___x_2857_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_2854_, v___x_2856_, v_kind_2839_, v_a_2841_, v_a_2842_);
return v___x_2857_;
}
else
{
lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec(v_a_2852_);
lean_dec(v_a_2850_);
v___x_2858_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1);
v___x_2859_ = 0;
v___x_2860_ = l_Lean_MessageData_ofConstName(v_declName_2838_, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2858_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2863_, v_a_2841_, v_a_2842_);
return v___x_2864_;
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_declName_2838_);
v_a_2865_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2867_ = v___x_2849_;
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2849_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2869_ = lean_io_error_to_string(v_a_2865_);
v___x_2870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
v___x_2871_ = l_Lean_MessageData_ofFormat(v___x_2870_);
lean_inc(v_ref_2847_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v_ref_2847_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2872_);
v___x_2874_ = v___x_2867_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object* v_declName_2877_, lean_object* v_kind_2878_, lean_object* v_phase_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
uint8_t v_kind_boxed_2883_; uint8_t v_phase_boxed_2884_; lean_object* v_res_2885_; 
v_kind_boxed_2883_ = lean_unbox(v_kind_2878_);
v_phase_boxed_2884_ = lean_unbox(v_phase_2879_);
v_res_2885_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2877_, v_kind_boxed_2883_, v_phase_boxed_2884_, v_a_2880_, v_a_2881_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object* v_stx_2898_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = l_Lean_Syntax_isNone(v_stx_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v_inner_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2900_ = lean_unsigned_to_nat(0u);
v_inner_2901_ = l_Lean_Syntax_getArg(v_stx_2898_, v___x_2900_);
v___x_2902_ = l_Lean_Syntax_getKind(v_inner_2901_);
v___x_2903_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2));
v___x_2904_ = lean_name_eq(v___x_2902_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4));
v___x_2906_ = lean_name_eq(v___x_2902_, v___x_2905_);
lean_dec(v___x_2902_);
if (v___x_2906_ == 0)
{
uint8_t v___x_2907_; 
v___x_2907_ = 2;
return v___x_2907_;
}
else
{
uint8_t v___x_2908_; 
v___x_2908_ = 1;
return v___x_2908_;
}
}
else
{
uint8_t v___x_2909_; 
lean_dec(v___x_2902_);
v___x_2909_ = 0;
return v___x_2909_;
}
}
else
{
uint8_t v___x_2910_; 
v___x_2910_ = 2;
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object* v_stx_2911_){
_start:
{
uint8_t v_res_2912_; lean_object* v_r_2913_; 
v_res_2912_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_2911_);
lean_dec(v_stx_2911_);
v_r_2913_ = lean_box(v_res_2912_);
return v_r_2913_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2918_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
lean_ctor_set(v___x_2918_, 2, v___x_2917_);
lean_ctor_set(v___x_2918_, 3, v___x_2917_);
lean_ctor_set(v___x_2918_, 4, v___x_2917_);
lean_ctor_set(v___x_2918_, 5, v___x_2917_);
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = lean_unsigned_to_nat(32u);
v___x_2920_ = lean_mk_empty_array_with_capacity(v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4(void){
_start:
{
size_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2922_ = ((size_t)5ULL);
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = lean_unsigned_to_nat(32u);
v___x_2925_ = lean_mk_empty_array_with_capacity(v___x_2924_);
v___x_2926_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3);
v___x_2927_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v___x_2925_);
lean_ctor_set(v___x_2927_, 2, v___x_2923_);
lean_ctor_set(v___x_2927_, 3, v___x_2923_);
lean_ctor_set_usize(v___x_2927_, 4, v___x_2922_);
return v___x_2927_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
lean_ctor_set(v___x_2929_, 2, v___x_2928_);
lean_ctor_set(v___x_2929_, 3, v___x_2928_);
lean_ctor_set(v___x_2929_, 4, v___x_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2930_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5);
v___x_2931_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4);
v___x_2932_ = lean_box(1);
v___x_2933_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2);
v___x_2934_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v___x_2933_);
lean_ctor_set(v___x_2935_, 2, v___x_2932_);
lean_ctor_set(v___x_2935_, 3, v___x_2931_);
lean_ctor_set(v___x_2935_, 4, v___x_2930_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object* v_declName_2936_, lean_object* v_stx_2937_, uint8_t v_attrKind_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1));
lean_inc(v_declName_2936_);
v___x_2943_ = l_Lean_ensureAttrDeclIsMeta(v___x_2942_, v_declName_2936_, v_attrKind_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
lean_dec_ref_known(v___x_2943_, 1);
v___x_2944_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_2945_ = lean_st_mk_ref(v___x_2944_);
v___x_2946_ = lean_unsigned_to_nat(1u);
v___x_2947_ = l_Lean_Syntax_getArg(v_stx_2937_, v___x_2946_);
v___x_2948_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_2947_);
lean_dec(v___x_2947_);
v___x_2949_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2936_, v_attrKind_2938_, v___x_2948_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2958_; 
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v___x_2949_, 0);
lean_dec(v_unused_2959_);
v___x_2951_ = v___x_2949_;
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
else
{
lean_dec(v___x_2949_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2953_ = lean_st_ref_get(v___x_2945_);
lean_dec(v___x_2945_);
lean_dec(v___x_2953_);
v___x_2954_ = lean_box(0);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2954_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
else
{
lean_dec(v___x_2945_);
return v___x_2949_;
}
}
else
{
lean_dec(v_declName_2936_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object* v_declName_2960_, lean_object* v_stx_2961_, lean_object* v_attrKind_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
uint8_t v_attrKind_boxed_2966_; lean_object* v_res_2967_; 
v_attrKind_boxed_2966_ = lean_unbox(v_attrKind_2962_);
v_res_2967_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_2960_, v_stx_2961_, v_attrKind_boxed_2966_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_stx_2961_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object* v_ref_2970_, lean_object* v_declName_2971_, uint8_t v_phase_2972_, lean_object* v_proc_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_keys_2977_; lean_object* v___x_2978_; 
v___x_2975_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_2976_ = lean_st_ref_get(v___x_2975_);
v_keys_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc_ref(v_keys_2977_);
lean_dec(v___x_2976_);
v___x_2978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_2977_, v_declName_2971_);
lean_dec_ref(v_keys_2977_);
if (lean_obj_tag(v___x_2978_) == 1)
{
lean_object* v_val_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2989_; 
v_val_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2989_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_val_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2989_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2983_ = lean_st_ref_take(v_ref_2970_);
v___x_2984_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v___x_2983_, v_val_2979_, v_declName_2971_, v_phase_2972_, v_proc_2973_);
v___x_2985_ = lean_st_ref_set(v_ref_2970_, v___x_2984_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2985_);
v___x_2987_ = v___x_2981_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v___x_2978_);
lean_dec_ref(v_proc_2973_);
v___x_2990_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0));
v___x_2991_ = l_Lean_privateToUserName(v_declName_2971_);
v___x_2992_ = 1;
v___x_2993_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2991_, v___x_2992_);
v___x_2994_ = lean_string_append(v___x_2990_, v___x_2993_);
lean_dec_ref(v___x_2993_);
v___x_2995_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1));
v___x_2996_ = lean_string_append(v___x_2994_, v___x_2995_);
v___x_2997_ = lean_mk_io_user_error(v___x_2996_);
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object* v_ref_2999_, lean_object* v_declName_3000_, lean_object* v_phase_3001_, lean_object* v_proc_3002_, lean_object* v_a_3003_){
_start:
{
uint8_t v_phase_boxed_3004_; lean_object* v_res_3005_; 
v_phase_boxed_3004_ = lean_unbox(v_phase_3001_);
v_res_3005_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_2999_, v_declName_3000_, v_phase_boxed_3004_, v_proc_3002_);
lean_dec(v_ref_2999_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object* v_declName_3006_, uint8_t v_phase_3007_, lean_object* v_proc_3008_){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___x_3011_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v___x_3010_, v_declName_3006_, v_phase_3007_, v_proc_3008_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object* v_declName_3012_, lean_object* v_phase_3013_, lean_object* v_proc_3014_, lean_object* v_a_3015_){
_start:
{
uint8_t v_phase_boxed_3016_; lean_object* v_res_3017_; 
v_phase_boxed_3016_ = lean_unbox(v_phase_3013_);
v_res_3017_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_3012_, v_phase_boxed_3016_, v_proc_3014_);
return v_res_3017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_box(0);
v___x_3026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1));
v___x_3027_ = l_Lean_mkConst(v___x_3026_, v___x_3025_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object* v_declName_3031_, lean_object* v_stx_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v_phase_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___y_3043_; 
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = l_Lean_Syntax_getArg(v_stx_3032_, v___x_3036_);
v_phase_3038_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_3037_);
lean_dec(v___x_3037_);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
lean_inc(v_declName_3031_);
v___x_3041_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3031_);
switch(v_phase_3038_)
{
case 0:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
v___y_3043_ = v___x_3075_;
goto v___jp_3042_;
}
case 1:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
v___y_3043_ = v___x_3076_;
goto v___jp_3042_;
}
default: 
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
v___y_3043_ = v___x_3077_;
goto v___jp_3042_;
}
}
v___jp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3044_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_3045_ = lean_st_mk_ref(v___x_3044_);
lean_inc(v_declName_3031_);
v___x_3046_ = l_Lean_mkConst(v_declName_3031_, v___x_3039_);
v___x_3047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4));
v___x_3048_ = l_Lean_Name_append(v_declName_3031_, v___x_3047_);
v___x_3049_ = l_Lean_Core_mkFreshUserName(v___x_3048_, v_a_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_val_3056_; lean_object* v___x_3057_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
v___x_3051_ = lean_unsigned_to_nat(3u);
v___x_3052_ = lean_mk_empty_array_with_capacity(v___x_3051_);
v___x_3053_ = lean_array_push(v___x_3052_, v___x_3041_);
lean_inc_ref(v___y_3043_);
v___x_3054_ = lean_array_push(v___x_3053_, v___y_3043_);
v___x_3055_ = lean_array_push(v___x_3054_, v___x_3046_);
v_val_3056_ = l_Lean_mkAppN(v___x_3040_, v___x_3055_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_declareBuiltin(v_a_3050_, v_val_3056_, v_a_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3066_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = lean_st_ref_get(v___x_3045_);
lean_dec(v___x_3045_);
lean_dec(v___x_3062_);
if (v_isShared_3061_ == 0)
{
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3058_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
else
{
lean_dec(v___x_3045_);
return v___x_3057_;
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___x_3046_);
lean_dec(v___x_3045_);
lean_dec_ref(v___x_3041_);
v_a_3067_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3049_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3049_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object* v_declName_3078_, lean_object* v_stx_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3078_, v_stx_3079_, v_a_3080_, v_a_3081_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_stx_3079_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3170_ = l_Lean_registerBuiltinAttribute(v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_declName_3173_, lean_object* v_stx_3174_, uint8_t v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3173_, v_stx_3174_, v___y_3176_, v___y_3177_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_declName_3180_, lean_object* v_stx_3181_, lean_object* v_x_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_x_116__boxed_3186_; lean_object* v_res_3187_; 
v_x_116__boxed_3186_ = lean_unbox(v_x_3182_);
v_res_3187_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3180_, v_stx_3181_, v_x_116__boxed_3186_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v_stx_3181_);
return v_res_3187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_x_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3196_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3195_, v___y_3192_, v___y_3193_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_x_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v_x_3197_);
return v_res_3201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_unsigned_to_nat(3124561870u);
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3206_ = l_Lean_Name_num___override(v___x_3205_, v___x_3204_);
return v___x_3206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3209_ = l_Lean_Name_str___override(v___x_3208_, v___x_3207_);
return v___x_3209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3212_ = l_Lean_Name_str___override(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_unsigned_to_nat(2u);
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3215_ = l_Lean_Name_num___override(v___x_3214_, v___x_3213_);
return v___x_3215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3220_ = 1;
v___x_3221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3224_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3222_);
lean_ctor_set(v___x_3224_, 2, v___x_3221_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*3, v___x_3220_);
return v___x_3224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3225_; lean_object* v___f_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___f_3225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___f_3226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___f_3226_);
lean_ctor_set(v___x_3228_, 2, v___f_3225_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3231_ = l_Lean_registerBuiltinAttribute(v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_a_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; lean_object* v_env_3237_; lean_object* v___x_3238_; lean_object* v_ext_3239_; lean_object* v_toEnvExtension_3240_; lean_object* v_asyncMode_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3236_ = lean_st_ref_get(v_a_3234_);
v_env_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc_ref(v_env_3237_);
lean_dec(v___x_3236_);
v___x_3238_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_3239_ = lean_ctor_get(v___x_3238_, 1);
v_toEnvExtension_3240_ = lean_ctor_get(v_ext_3239_, 0);
v_asyncMode_3241_ = lean_ctor_get(v_toEnvExtension_3240_, 2);
v___x_3242_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_3243_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3242_, v___x_3238_, v_env_3237_, v_asyncMode_3241_);
v___x_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3245_);
lean_dec(v_a_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
return v_res_3255_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = lean_unsigned_to_nat(32u);
v___x_3257_ = lean_mk_empty_array_with_capacity(v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
return v___x_3258_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3259_ = ((size_t)5ULL);
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_unsigned_to_nat(32u);
v___x_3262_ = lean_mk_empty_array_with_capacity(v___x_3261_);
v___x_3263_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0);
v___x_3264_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
lean_ctor_set(v___x_3264_, 1, v___x_3262_);
lean_ctor_set(v___x_3264_, 2, v___x_3260_);
lean_ctor_set(v___x_3264_, 3, v___x_3260_);
lean_ctor_set_usize(v___x_3264_, 4, v___x_3259_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; lean_object* v_traceState_3268_; lean_object* v_traces_3269_; lean_object* v___x_3270_; lean_object* v_traceState_3271_; lean_object* v_env_3272_; lean_object* v_nextMacroScope_3273_; lean_object* v_ngen_3274_; lean_object* v_auxDeclNGen_3275_; lean_object* v_cache_3276_; lean_object* v_messages_3277_; lean_object* v_infoState_3278_; lean_object* v_snapshotTasks_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3298_; 
v___x_3267_ = lean_st_ref_get(v___y_3265_);
v_traceState_3268_ = lean_ctor_get(v___x_3267_, 4);
lean_inc_ref(v_traceState_3268_);
lean_dec(v___x_3267_);
v_traces_3269_ = lean_ctor_get(v_traceState_3268_, 0);
lean_inc_ref(v_traces_3269_);
lean_dec_ref(v_traceState_3268_);
v___x_3270_ = lean_st_ref_take(v___y_3265_);
v_traceState_3271_ = lean_ctor_get(v___x_3270_, 4);
v_env_3272_ = lean_ctor_get(v___x_3270_, 0);
v_nextMacroScope_3273_ = lean_ctor_get(v___x_3270_, 1);
v_ngen_3274_ = lean_ctor_get(v___x_3270_, 2);
v_auxDeclNGen_3275_ = lean_ctor_get(v___x_3270_, 3);
v_cache_3276_ = lean_ctor_get(v___x_3270_, 5);
v_messages_3277_ = lean_ctor_get(v___x_3270_, 6);
v_infoState_3278_ = lean_ctor_get(v___x_3270_, 7);
v_snapshotTasks_3279_ = lean_ctor_get(v___x_3270_, 8);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3281_ = v___x_3270_;
v_isShared_3282_ = v_isSharedCheck_3298_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_snapshotTasks_3279_);
lean_inc(v_infoState_3278_);
lean_inc(v_messages_3277_);
lean_inc(v_cache_3276_);
lean_inc(v_traceState_3271_);
lean_inc(v_auxDeclNGen_3275_);
lean_inc(v_ngen_3274_);
lean_inc(v_nextMacroScope_3273_);
lean_inc(v_env_3272_);
lean_dec(v___x_3270_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3298_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
uint64_t v_tid_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3296_; 
v_tid_3283_ = lean_ctor_get_uint64(v_traceState_3271_, sizeof(void*)*1);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_traceState_3271_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; 
v_unused_3297_ = lean_ctor_get(v_traceState_3271_, 0);
lean_dec(v_unused_3297_);
v___x_3285_ = v_traceState_3271_;
v_isShared_3286_ = v_isSharedCheck_3296_;
goto v_resetjp_3284_;
}
else
{
lean_dec(v_traceState_3271_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3296_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3287_);
v___x_3289_ = v___x_3285_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3287_);
lean_ctor_set_uint64(v_reuseFailAlloc_3295_, sizeof(void*)*1, v_tid_3283_);
v___x_3289_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3291_; 
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 4, v___x_3289_);
v___x_3291_ = v___x_3281_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_env_3272_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_nextMacroScope_3273_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_ngen_3274_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_auxDeclNGen_3275_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3294_, 5, v_cache_3276_);
lean_ctor_set(v_reuseFailAlloc_3294_, 6, v_messages_3277_);
lean_ctor_set(v_reuseFailAlloc_3294_, 7, v_infoState_3278_);
lean_ctor_set(v_reuseFailAlloc_3294_, 8, v_snapshotTasks_3279_);
v___x_3291_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_st_ref_set(v___y_3265_, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_traces_3269_);
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3299_);
lean_dec(v___y_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
return v_res_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object* v_opts_3324_, lean_object* v_opt_3325_){
_start:
{
lean_object* v_name_3326_; lean_object* v_defValue_3327_; lean_object* v_map_3328_; lean_object* v___x_3329_; 
v_name_3326_ = lean_ctor_get(v_opt_3325_, 0);
v_defValue_3327_ = lean_ctor_get(v_opt_3325_, 1);
v_map_3328_ = lean_ctor_get(v_opts_3324_, 0);
v___x_3329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3328_, v_name_3326_);
if (lean_obj_tag(v___x_3329_) == 0)
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_unbox(v_defValue_3327_);
return v___x_3330_;
}
else
{
lean_object* v_val_3331_; 
v_val_3331_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___x_3329_, 1);
if (lean_obj_tag(v_val_3331_) == 1)
{
uint8_t v_v_3332_; 
v_v_3332_ = lean_ctor_get_uint8(v_val_3331_, 0);
lean_dec_ref_known(v_val_3331_, 0);
return v_v_3332_;
}
else
{
uint8_t v___x_3333_; 
lean_dec(v_val_3331_);
v___x_3333_ = lean_unbox(v_defValue_3327_);
return v___x_3333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object* v_opts_3334_, lean_object* v_opt_3335_){
_start:
{
uint8_t v_res_3336_; lean_object* v_r_3337_; 
v_res_3336_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3334_, v_opt_3335_);
lean_dec_ref(v_opt_3335_);
lean_dec_ref(v_opts_3334_);
v_r_3337_ = lean_box(v_res_3336_);
return v_r_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t v___x_3338_, lean_object* v_e_3339_, lean_object* v_snd_3340_, lean_object* v_proc_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
if (v___x_3338_ == 0)
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_3339_, v_snd_3340_, v_proc_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
return v___x_3352_;
}
else
{
lean_object* v___x_3353_; 
lean_inc(v___y_3350_);
lean_inc_ref(v___y_3349_);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
v___x_3353_ = lean_apply_11(v_proc_3341_, v_e_3339_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, lean_box(0));
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object* v___x_3354_, lean_object* v_e_3355_, lean_object* v_snd_3356_, lean_object* v_proc_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
uint8_t v___x_48928__boxed_3368_; lean_object* v_res_3369_; 
v___x_48928__boxed_3368_ = lean_unbox(v___x_3354_);
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_48928__boxed_3368_, v_e_3355_, v_snd_3356_, v_proc_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v_snd_3356_);
return v_res_3369_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object* v_e_3370_){
_start:
{
if (lean_obj_tag(v_e_3370_) == 0)
{
uint8_t v___x_3371_; 
v___x_3371_ = 2;
return v___x_3371_;
}
else
{
uint8_t v___x_3372_; 
v___x_3372_ = 0;
return v___x_3372_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object* v_e_3373_){
_start:
{
uint8_t v_res_3374_; lean_object* v_r_3375_; 
v_res_3374_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_e_3373_);
lean_dec_ref(v_e_3373_);
v_r_3375_ = lean_box(v_res_3374_);
return v_r_3375_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
v_a_3378_ = lean_ctor_get(v_x_3376_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_x_3376_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v_x_3376_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v_x_3376_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 1);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v_a_3386_ = lean_ctor_get(v_x_3376_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_x_3376_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v_x_3376_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v_x_3376_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 0);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object* v_x_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t v_sz_3397_, size_t v_i_3398_, lean_object* v_bs_3399_){
_start:
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_usize_dec_lt(v_i_3398_, v_sz_3397_);
if (v___x_3400_ == 0)
{
return v_bs_3399_;
}
else
{
lean_object* v_v_3401_; lean_object* v_msg_3402_; lean_object* v___x_3403_; lean_object* v_bs_x27_3404_; size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; 
v_v_3401_ = lean_array_uget_borrowed(v_bs_3399_, v_i_3398_);
v_msg_3402_ = lean_ctor_get(v_v_3401_, 1);
lean_inc_ref(v_msg_3402_);
v___x_3403_ = lean_unsigned_to_nat(0u);
v_bs_x27_3404_ = lean_array_uset(v_bs_3399_, v_i_3398_, v___x_3403_);
v___x_3405_ = ((size_t)1ULL);
v___x_3406_ = lean_usize_add(v_i_3398_, v___x_3405_);
v___x_3407_ = lean_array_uset(v_bs_x27_3404_, v_i_3398_, v_msg_3402_);
v_i_3398_ = v___x_3406_;
v_bs_3399_ = v___x_3407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_3409_, lean_object* v_i_3410_, lean_object* v_bs_3411_){
_start:
{
size_t v_sz_boxed_3412_; size_t v_i_boxed_3413_; lean_object* v_res_3414_; 
v_sz_boxed_3412_ = lean_unbox_usize(v_sz_3409_);
lean_dec(v_sz_3409_);
v_i_boxed_3413_ = lean_unbox_usize(v_i_3410_);
lean_dec(v_i_3410_);
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_boxed_3412_, v_i_boxed_3413_, v_bs_3411_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object* v_msgData_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; lean_object* v_env_3422_; lean_object* v___x_3423_; lean_object* v_mctx_3424_; lean_object* v_lctx_3425_; lean_object* v_options_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3421_ = lean_st_ref_get(v___y_3419_);
v_env_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc_ref(v_env_3422_);
lean_dec(v___x_3421_);
v___x_3423_ = lean_st_ref_get(v___y_3417_);
v_mctx_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_mctx_3424_);
lean_dec(v___x_3423_);
v_lctx_3425_ = lean_ctor_get(v___y_3416_, 2);
v_options_3426_ = lean_ctor_get(v___y_3418_, 2);
lean_inc_ref(v_options_3426_);
lean_inc_ref(v_lctx_3425_);
v___x_3427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3427_, 0, v_env_3422_);
lean_ctor_set(v___x_3427_, 1, v_mctx_3424_);
lean_ctor_set(v___x_3427_, 2, v_lctx_3425_);
lean_ctor_set(v___x_3427_, 3, v_options_3426_);
v___x_3428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v_msgData_3415_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msgData_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object* v_oldTraces_3437_, lean_object* v_data_3438_, lean_object* v_ref_3439_, lean_object* v_msg_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_fileName_3446_; lean_object* v_fileMap_3447_; lean_object* v_options_3448_; lean_object* v_currRecDepth_3449_; lean_object* v_maxRecDepth_3450_; lean_object* v_ref_3451_; lean_object* v_currNamespace_3452_; lean_object* v_openDecls_3453_; lean_object* v_initHeartbeats_3454_; lean_object* v_maxHeartbeats_3455_; lean_object* v_quotContext_3456_; lean_object* v_currMacroScope_3457_; uint8_t v_diag_3458_; lean_object* v_cancelTk_x3f_3459_; uint8_t v_suppressElabErrors_3460_; lean_object* v_inheritedTraceOptions_3461_; lean_object* v___x_3462_; lean_object* v_traceState_3463_; lean_object* v_traces_3464_; lean_object* v_ref_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; size_t v_sz_3468_; size_t v___x_3469_; lean_object* v___x_3470_; lean_object* v_msg_3471_; lean_object* v___x_3472_; lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3510_; 
v_fileName_3446_ = lean_ctor_get(v___y_3443_, 0);
v_fileMap_3447_ = lean_ctor_get(v___y_3443_, 1);
v_options_3448_ = lean_ctor_get(v___y_3443_, 2);
v_currRecDepth_3449_ = lean_ctor_get(v___y_3443_, 3);
v_maxRecDepth_3450_ = lean_ctor_get(v___y_3443_, 4);
v_ref_3451_ = lean_ctor_get(v___y_3443_, 5);
v_currNamespace_3452_ = lean_ctor_get(v___y_3443_, 6);
v_openDecls_3453_ = lean_ctor_get(v___y_3443_, 7);
v_initHeartbeats_3454_ = lean_ctor_get(v___y_3443_, 8);
v_maxHeartbeats_3455_ = lean_ctor_get(v___y_3443_, 9);
v_quotContext_3456_ = lean_ctor_get(v___y_3443_, 10);
v_currMacroScope_3457_ = lean_ctor_get(v___y_3443_, 11);
v_diag_3458_ = lean_ctor_get_uint8(v___y_3443_, sizeof(void*)*14);
v_cancelTk_x3f_3459_ = lean_ctor_get(v___y_3443_, 12);
v_suppressElabErrors_3460_ = lean_ctor_get_uint8(v___y_3443_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3461_ = lean_ctor_get(v___y_3443_, 13);
v___x_3462_ = lean_st_ref_get(v___y_3444_);
v_traceState_3463_ = lean_ctor_get(v___x_3462_, 4);
lean_inc_ref(v_traceState_3463_);
lean_dec(v___x_3462_);
v_traces_3464_ = lean_ctor_get(v_traceState_3463_, 0);
lean_inc_ref(v_traces_3464_);
lean_dec_ref(v_traceState_3463_);
v_ref_3465_ = l_Lean_replaceRef(v_ref_3439_, v_ref_3451_);
lean_inc_ref(v_inheritedTraceOptions_3461_);
lean_inc(v_cancelTk_x3f_3459_);
lean_inc(v_currMacroScope_3457_);
lean_inc(v_quotContext_3456_);
lean_inc(v_maxHeartbeats_3455_);
lean_inc(v_initHeartbeats_3454_);
lean_inc(v_openDecls_3453_);
lean_inc(v_currNamespace_3452_);
lean_inc(v_maxRecDepth_3450_);
lean_inc(v_currRecDepth_3449_);
lean_inc_ref(v_options_3448_);
lean_inc_ref(v_fileMap_3447_);
lean_inc_ref(v_fileName_3446_);
v___x_3466_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3466_, 0, v_fileName_3446_);
lean_ctor_set(v___x_3466_, 1, v_fileMap_3447_);
lean_ctor_set(v___x_3466_, 2, v_options_3448_);
lean_ctor_set(v___x_3466_, 3, v_currRecDepth_3449_);
lean_ctor_set(v___x_3466_, 4, v_maxRecDepth_3450_);
lean_ctor_set(v___x_3466_, 5, v_ref_3465_);
lean_ctor_set(v___x_3466_, 6, v_currNamespace_3452_);
lean_ctor_set(v___x_3466_, 7, v_openDecls_3453_);
lean_ctor_set(v___x_3466_, 8, v_initHeartbeats_3454_);
lean_ctor_set(v___x_3466_, 9, v_maxHeartbeats_3455_);
lean_ctor_set(v___x_3466_, 10, v_quotContext_3456_);
lean_ctor_set(v___x_3466_, 11, v_currMacroScope_3457_);
lean_ctor_set(v___x_3466_, 12, v_cancelTk_x3f_3459_);
lean_ctor_set(v___x_3466_, 13, v_inheritedTraceOptions_3461_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*14, v_diag_3458_);
lean_ctor_set_uint8(v___x_3466_, sizeof(void*)*14 + 1, v_suppressElabErrors_3460_);
v___x_3467_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3464_);
lean_dec_ref(v_traces_3464_);
v_sz_3468_ = lean_array_size(v___x_3467_);
v___x_3469_ = ((size_t)0ULL);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_3468_, v___x_3469_, v___x_3467_);
v_msg_3471_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3471_, 0, v_data_3438_);
lean_ctor_set(v_msg_3471_, 1, v_msg_3440_);
lean_ctor_set(v_msg_3471_, 2, v___x_3470_);
v___x_3472_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msg_3471_, v___y_3441_, v___y_3442_, v___x_3466_, v___y_3444_);
lean_dec_ref_known(v___x_3466_, 14);
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3510_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3510_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v_traceState_3478_; lean_object* v_env_3479_; lean_object* v_nextMacroScope_3480_; lean_object* v_ngen_3481_; lean_object* v_auxDeclNGen_3482_; lean_object* v_cache_3483_; lean_object* v_messages_3484_; lean_object* v_infoState_3485_; lean_object* v_snapshotTasks_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3509_; 
v___x_3477_ = lean_st_ref_take(v___y_3444_);
v_traceState_3478_ = lean_ctor_get(v___x_3477_, 4);
v_env_3479_ = lean_ctor_get(v___x_3477_, 0);
v_nextMacroScope_3480_ = lean_ctor_get(v___x_3477_, 1);
v_ngen_3481_ = lean_ctor_get(v___x_3477_, 2);
v_auxDeclNGen_3482_ = lean_ctor_get(v___x_3477_, 3);
v_cache_3483_ = lean_ctor_get(v___x_3477_, 5);
v_messages_3484_ = lean_ctor_get(v___x_3477_, 6);
v_infoState_3485_ = lean_ctor_get(v___x_3477_, 7);
v_snapshotTasks_3486_ = lean_ctor_get(v___x_3477_, 8);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3488_ = v___x_3477_;
v_isShared_3489_ = v_isSharedCheck_3509_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_snapshotTasks_3486_);
lean_inc(v_infoState_3485_);
lean_inc(v_messages_3484_);
lean_inc(v_cache_3483_);
lean_inc(v_traceState_3478_);
lean_inc(v_auxDeclNGen_3482_);
lean_inc(v_ngen_3481_);
lean_inc(v_nextMacroScope_3480_);
lean_inc(v_env_3479_);
lean_dec(v___x_3477_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3509_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
uint64_t v_tid_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3507_; 
v_tid_3490_ = lean_ctor_get_uint64(v_traceState_3478_, sizeof(void*)*1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_traceState_3478_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; 
v_unused_3508_ = lean_ctor_get(v_traceState_3478_, 0);
lean_dec(v_unused_3508_);
v___x_3492_ = v_traceState_3478_;
v_isShared_3493_ = v_isSharedCheck_3507_;
goto v_resetjp_3491_;
}
else
{
lean_dec(v_traceState_3478_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3507_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v_ref_3439_);
lean_ctor_set(v___x_3494_, 1, v_a_3473_);
v___x_3495_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3437_, v___x_3494_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3495_);
v___x_3497_ = v___x_3492_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3495_);
lean_ctor_set_uint64(v_reuseFailAlloc_3506_, sizeof(void*)*1, v_tid_3490_);
v___x_3497_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 4, v___x_3497_);
v___x_3499_ = v___x_3488_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_env_3479_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_nextMacroScope_3480_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_ngen_3481_);
lean_ctor_set(v_reuseFailAlloc_3505_, 3, v_auxDeclNGen_3482_);
lean_ctor_set(v_reuseFailAlloc_3505_, 4, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3505_, 5, v_cache_3483_);
lean_ctor_set(v_reuseFailAlloc_3505_, 6, v_messages_3484_);
lean_ctor_set(v_reuseFailAlloc_3505_, 7, v_infoState_3485_);
lean_ctor_set(v_reuseFailAlloc_3505_, 8, v_snapshotTasks_3486_);
v___x_3499_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3500_ = lean_st_ref_set(v___y_3444_, v___x_3499_);
v___x_3501_ = lean_box(0);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3501_);
v___x_3503_ = v___x_3475_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_3511_, lean_object* v_data_3512_, lean_object* v_ref_3513_, lean_object* v_msg_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3511_, v_data_3512_, v_ref_3513_, v_msg_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object* v_opts_3521_, lean_object* v_opt_3522_){
_start:
{
lean_object* v_name_3523_; lean_object* v_defValue_3524_; lean_object* v_map_3525_; lean_object* v___x_3526_; 
v_name_3523_ = lean_ctor_get(v_opt_3522_, 0);
v_defValue_3524_ = lean_ctor_get(v_opt_3522_, 1);
v_map_3525_ = lean_ctor_get(v_opts_3521_, 0);
v___x_3526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3525_, v_name_3523_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_inc(v_defValue_3524_);
return v_defValue_3524_;
}
else
{
lean_object* v_val_3527_; 
v_val_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_val_3527_);
lean_dec_ref_known(v___x_3526_, 1);
if (lean_obj_tag(v_val_3527_) == 3)
{
lean_object* v_v_3528_; 
v_v_3528_ = lean_ctor_get(v_val_3527_, 0);
lean_inc(v_v_3528_);
lean_dec_ref_known(v_val_3527_, 1);
return v_v_3528_;
}
else
{
lean_dec(v_val_3527_);
lean_inc(v_defValue_3524_);
return v_defValue_3524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object* v_opts_3529_, lean_object* v_opt_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3529_, v_opt_3530_);
lean_dec_ref(v_opt_3530_);
lean_dec_ref(v_opts_3529_);
return v_res_3531_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3532_; double v___x_3533_; 
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = lean_float_of_nat(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3537_; double v___x_3538_; 
v___x_3537_ = lean_unsigned_to_nat(1000u);
v___x_3538_ = lean_float_of_nat(v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object* v_cls_3539_, uint8_t v_collapsed_3540_, lean_object* v_tag_3541_, lean_object* v_opts_3542_, uint8_t v_clsEnabled_3543_, lean_object* v_oldTraces_3544_, lean_object* v_msg_3545_, lean_object* v_resStartStop_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_fst_3557_; lean_object* v_snd_3558_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v_data_3562_; lean_object* v_fst_3573_; lean_object* v_snd_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; lean_object* v___y_3578_; lean_object* v_a_3579_; uint8_t v___y_3594_; double v___y_3625_; 
v_fst_3557_ = lean_ctor_get(v_resStartStop_3546_, 0);
lean_inc(v_fst_3557_);
v_snd_3558_ = lean_ctor_get(v_resStartStop_3546_, 1);
lean_inc(v_snd_3558_);
lean_dec_ref(v_resStartStop_3546_);
v_fst_3573_ = lean_ctor_get(v_snd_3558_, 0);
lean_inc(v_fst_3573_);
v_snd_3574_ = lean_ctor_get(v_snd_3558_, 1);
lean_inc(v_snd_3574_);
lean_dec(v_snd_3558_);
v___x_3575_ = l_Lean_trace_profiler;
v___x_3576_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3542_, v___x_3575_);
if (v___x_3576_ == 0)
{
v___y_3594_ = v___x_3576_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3631_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3542_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3633_; double v___x_3634_; double v___x_3635_; double v___x_3636_; 
v___x_3632_ = l_Lean_trace_profiler_threshold;
v___x_3633_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3542_, v___x_3632_);
v___x_3634_ = lean_float_of_nat(v___x_3633_);
v___x_3635_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3);
v___x_3636_ = lean_float_div(v___x_3634_, v___x_3635_);
v___y_3625_ = v___x_3636_;
goto v___jp_3624_;
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; double v___x_3639_; 
v___x_3637_ = l_Lean_trace_profiler_threshold;
v___x_3638_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3542_, v___x_3637_);
v___x_3639_ = lean_float_of_nat(v___x_3638_);
v___y_3625_ = v___x_3639_;
goto v___jp_3624_;
}
}
v___jp_3559_:
{
lean_object* v___x_3563_; 
lean_inc(v___y_3561_);
v___x_3563_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3544_, v_data_3562_, v___y_3561_, v___y_3560_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref_known(v___x_3563_, 1);
v___x_3564_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3557_);
return v___x_3564_;
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec(v_fst_3557_);
v_a_3565_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3563_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3563_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
v___jp_3577_:
{
uint8_t v_result_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; double v___x_3583_; lean_object* v_data_3584_; 
v_result_3580_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_fst_3557_);
v___x_3581_ = lean_box(v_result_3580_);
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
v___x_3583_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0);
lean_inc_ref(v_tag_3541_);
lean_inc_ref(v___x_3582_);
lean_inc(v_cls_3539_);
v_data_3584_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3584_, 0, v_cls_3539_);
lean_ctor_set(v_data_3584_, 1, v___x_3582_);
lean_ctor_set(v_data_3584_, 2, v_tag_3541_);
lean_ctor_set_float(v_data_3584_, sizeof(void*)*3, v___x_3583_);
lean_ctor_set_float(v_data_3584_, sizeof(void*)*3 + 8, v___x_3583_);
lean_ctor_set_uint8(v_data_3584_, sizeof(void*)*3 + 16, v_collapsed_3540_);
if (v___x_3576_ == 0)
{
lean_dec_ref_known(v___x_3582_, 1);
lean_dec(v_snd_3574_);
lean_dec(v_fst_3573_);
lean_dec_ref(v_tag_3541_);
lean_dec(v_cls_3539_);
v___y_3560_ = v_a_3579_;
v___y_3561_ = v___y_3578_;
v_data_3562_ = v_data_3584_;
goto v___jp_3559_;
}
else
{
lean_object* v_data_3585_; double v___x_3586_; double v___x_3587_; 
lean_dec_ref_known(v_data_3584_, 3);
v_data_3585_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3585_, 0, v_cls_3539_);
lean_ctor_set(v_data_3585_, 1, v___x_3582_);
lean_ctor_set(v_data_3585_, 2, v_tag_3541_);
v___x_3586_ = lean_unbox_float(v_fst_3573_);
lean_dec(v_fst_3573_);
lean_ctor_set_float(v_data_3585_, sizeof(void*)*3, v___x_3586_);
v___x_3587_ = lean_unbox_float(v_snd_3574_);
lean_dec(v_snd_3574_);
lean_ctor_set_float(v_data_3585_, sizeof(void*)*3 + 8, v___x_3587_);
lean_ctor_set_uint8(v_data_3585_, sizeof(void*)*3 + 16, v_collapsed_3540_);
v___y_3560_ = v_a_3579_;
v___y_3561_ = v___y_3578_;
v_data_3562_ = v_data_3585_;
goto v___jp_3559_;
}
}
v___jp_3588_:
{
lean_object* v_ref_3589_; lean_object* v___x_3590_; 
v_ref_3589_ = lean_ctor_get(v___y_3554_, 5);
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3554_);
lean_inc(v___y_3553_);
lean_inc_ref(v___y_3552_);
lean_inc(v___y_3551_);
lean_inc_ref(v___y_3550_);
lean_inc(v___y_3549_);
lean_inc_ref(v___y_3548_);
lean_inc(v___y_3547_);
lean_inc(v_fst_3557_);
v___x_3590_ = lean_apply_11(v_msg_3545_, v_fst_3557_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, lean_box(0));
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v___y_3578_ = v_ref_3589_;
v_a_3579_ = v_a_3591_;
goto v___jp_3577_;
}
else
{
lean_object* v___x_3592_; 
lean_dec_ref_known(v___x_3590_, 1);
v___x_3592_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2);
v___y_3578_ = v_ref_3589_;
v_a_3579_ = v___x_3592_;
goto v___jp_3577_;
}
}
v___jp_3593_:
{
if (v_clsEnabled_3543_ == 0)
{
if (v___y_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v_traceState_3596_; lean_object* v_env_3597_; lean_object* v_nextMacroScope_3598_; lean_object* v_ngen_3599_; lean_object* v_auxDeclNGen_3600_; lean_object* v_cache_3601_; lean_object* v_messages_3602_; lean_object* v_infoState_3603_; lean_object* v_snapshotTasks_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_snd_3574_);
lean_dec(v_fst_3573_);
lean_dec_ref(v_msg_3545_);
lean_dec_ref(v_tag_3541_);
lean_dec(v_cls_3539_);
v___x_3595_ = lean_st_ref_take(v___y_3555_);
v_traceState_3596_ = lean_ctor_get(v___x_3595_, 4);
v_env_3597_ = lean_ctor_get(v___x_3595_, 0);
v_nextMacroScope_3598_ = lean_ctor_get(v___x_3595_, 1);
v_ngen_3599_ = lean_ctor_get(v___x_3595_, 2);
v_auxDeclNGen_3600_ = lean_ctor_get(v___x_3595_, 3);
v_cache_3601_ = lean_ctor_get(v___x_3595_, 5);
v_messages_3602_ = lean_ctor_get(v___x_3595_, 6);
v_infoState_3603_ = lean_ctor_get(v___x_3595_, 7);
v_snapshotTasks_3604_ = lean_ctor_get(v___x_3595_, 8);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3606_ = v___x_3595_;
v_isShared_3607_ = v_isSharedCheck_3623_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_snapshotTasks_3604_);
lean_inc(v_infoState_3603_);
lean_inc(v_messages_3602_);
lean_inc(v_cache_3601_);
lean_inc(v_traceState_3596_);
lean_inc(v_auxDeclNGen_3600_);
lean_inc(v_ngen_3599_);
lean_inc(v_nextMacroScope_3598_);
lean_inc(v_env_3597_);
lean_dec(v___x_3595_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3623_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
uint64_t v_tid_3608_; lean_object* v_traces_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3622_; 
v_tid_3608_ = lean_ctor_get_uint64(v_traceState_3596_, sizeof(void*)*1);
v_traces_3609_ = lean_ctor_get(v_traceState_3596_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_traceState_3596_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3611_ = v_traceState_3596_;
v_isShared_3612_ = v_isSharedCheck_3622_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_traces_3609_);
lean_dec(v_traceState_3596_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3622_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3544_, v_traces_3609_);
lean_dec_ref(v_traces_3609_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v___x_3613_);
v___x_3615_ = v___x_3611_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3613_);
lean_ctor_set_uint64(v_reuseFailAlloc_3621_, sizeof(void*)*1, v_tid_3608_);
v___x_3615_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 4, v___x_3615_);
v___x_3617_ = v___x_3606_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_env_3597_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_nextMacroScope_3598_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_ngen_3599_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_auxDeclNGen_3600_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3620_, 5, v_cache_3601_);
lean_ctor_set(v_reuseFailAlloc_3620_, 6, v_messages_3602_);
lean_ctor_set(v_reuseFailAlloc_3620_, 7, v_infoState_3603_);
lean_ctor_set(v_reuseFailAlloc_3620_, 8, v_snapshotTasks_3604_);
v___x_3617_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_st_ref_set(v___y_3555_, v___x_3617_);
v___x_3619_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3557_);
return v___x_3619_;
}
}
}
}
}
else
{
goto v___jp_3588_;
}
}
else
{
goto v___jp_3588_;
}
}
v___jp_3624_:
{
double v___x_3626_; double v___x_3627_; double v___x_3628_; uint8_t v___x_3629_; 
v___x_3626_ = lean_unbox_float(v_snd_3574_);
v___x_3627_ = lean_unbox_float(v_fst_3573_);
v___x_3628_ = lean_float_sub(v___x_3626_, v___x_3627_);
v___x_3629_ = lean_float_decLt(v___y_3625_, v___x_3628_);
v___y_3594_ = v___x_3629_;
goto v___jp_3593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object** _args){
lean_object* v_cls_3640_ = _args[0];
lean_object* v_collapsed_3641_ = _args[1];
lean_object* v_tag_3642_ = _args[2];
lean_object* v_opts_3643_ = _args[3];
lean_object* v_clsEnabled_3644_ = _args[4];
lean_object* v_oldTraces_3645_ = _args[5];
lean_object* v_msg_3646_ = _args[6];
lean_object* v_resStartStop_3647_ = _args[7];
lean_object* v___y_3648_ = _args[8];
lean_object* v___y_3649_ = _args[9];
lean_object* v___y_3650_ = _args[10];
lean_object* v___y_3651_ = _args[11];
lean_object* v___y_3652_ = _args[12];
lean_object* v___y_3653_ = _args[13];
lean_object* v___y_3654_ = _args[14];
lean_object* v___y_3655_ = _args[15];
lean_object* v___y_3656_ = _args[16];
lean_object* v___y_3657_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3658_; uint8_t v_clsEnabled_boxed_3659_; lean_object* v_res_3660_; 
v_collapsed_boxed_3658_ = lean_unbox(v_collapsed_3641_);
v_clsEnabled_boxed_3659_ = lean_unbox(v_clsEnabled_3644_);
v_res_3660_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_3640_, v_collapsed_boxed_3658_, v_tag_3642_, v_opts_3643_, v_clsEnabled_boxed_3659_, v_oldTraces_3645_, v_msg_3646_, v_resStartStop_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v_opts_3643_);
return v_res_3660_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0));
v___x_3663_ = l_Lean_stringToMessageData(v___x_3662_);
return v___x_3663_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2));
v___x_3666_ = l_Lean_stringToMessageData(v___x_3665_);
return v___x_3666_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4));
v___x_3669_ = l_Lean_stringToMessageData(v___x_3668_);
return v___x_3669_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6));
v___x_3672_ = l_Lean_stringToMessageData(v___x_3671_);
return v___x_3672_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8));
v___x_3675_ = l_Lean_stringToMessageData(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10));
v___x_3678_ = l_Lean_stringToMessageData(v___x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object* v___x_3679_, lean_object* v_e_3680_, lean_object* v_x_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
if (lean_obj_tag(v_x_3681_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3706_; 
lean_dec_ref(v_e_3680_);
v_a_3692_ = lean_ctor_get(v_x_3681_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_x_3681_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3694_ = v_x_3681_;
v_isShared_3695_ = v_isSharedCheck_3706_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v_x_3681_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3706_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3696_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3697_ = l_Lean_MessageData_ofName(v___x_3679_);
v___x_3698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = l_Lean_Exception_toMessageData(v_a_3692_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3702_);
v___x_3704_ = v___x_3694_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3745_; 
v_a_3707_ = lean_ctor_get(v_x_3681_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_x_3681_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3709_ = v_x_3681_;
v_isShared_3710_ = v_isSharedCheck_3745_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v_x_3681_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3745_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
if (lean_obj_tag(v_a_3707_) == 0)
{
uint8_t v_done_3711_; 
v_done_3711_ = lean_ctor_get_uint8(v_a_3707_, 0);
lean_dec_ref_known(v_a_3707_, 0);
if (v_done_3711_ == 1)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3713_ = l_Lean_MessageData_ofName(v___x_3679_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_indentExpr(v_e_3680_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set_tag(v___x_3709_, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3718_);
v___x_3720_ = v___x_3709_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec_ref(v_e_3680_);
v___x_3722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3723_ = l_Lean_MessageData_ofName(v___x_3679_);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set_tag(v___x_3709_, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3726_);
v___x_3728_ = v___x_3709_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_e_x27_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
v_e_x27_3730_ = lean_ctor_get(v_a_3707_, 0);
lean_inc_ref(v_e_x27_3730_);
lean_dec_ref_known(v_a_3707_, 2);
v___x_3731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3732_ = l_Lean_MessageData_ofName(v___x_3679_);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = l_Lean_indentExpr(v_e_3680_);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l_Lean_indentExpr(v_e_x27_3730_);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set_tag(v___x_3709_, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3741_);
v___x_3743_ = v___x_3709_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object* v___x_3746_, lean_object* v_e_3747_, lean_object* v_x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_3746_, v_e_3747_, v_x_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
return v_res_3759_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7(void){
_start:
{
lean_object* v___x_3781_; double v___x_3782_; 
v___x_3781_ = lean_unsigned_to_nat(1000000000u);
v___x_3782_ = lean_float_of_nat(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9));
v___x_3788_ = l_Lean_Name_append(v___x_3787_, v___x_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object* v_erased_3789_, lean_object* v_e_3790_, lean_object* v_as_3791_, size_t v_sz_3792_, size_t v_i_3793_, lean_object* v_b_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_a_3806_; uint8_t v___x_3810_; 
v___x_3810_ = lean_usize_dec_lt(v_i_3793_, v_sz_3792_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec_ref(v_e_3790_);
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_b_3794_);
return v___x_3811_;
}
else
{
lean_object* v_a_3812_; lean_object* v_fst_3813_; lean_object* v_toCbvSimprocOLeanEntry_3814_; lean_object* v_snd_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_b_3794_);
v_a_3812_ = lean_array_uget(v_as_3791_, v_i_3793_);
v_fst_3813_ = lean_ctor_get(v_a_3812_, 0);
lean_inc(v_fst_3813_);
v_toCbvSimprocOLeanEntry_3814_ = lean_ctor_get(v_fst_3813_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_3814_);
v_snd_3815_ = lean_ctor_get(v_a_3812_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_a_3812_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; 
v_unused_3963_ = lean_ctor_get(v_a_3812_, 0);
lean_dec(v_unused_3963_);
v___x_3817_ = v_a_3812_;
v_isShared_3818_ = v_isSharedCheck_3962_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_snd_3815_);
lean_dec(v_a_3812_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3962_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v_proc_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3960_; 
v_proc_3819_ = lean_ctor_get(v_fst_3813_, 1);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_fst_3813_);
if (v_isSharedCheck_3960_ == 0)
{
lean_object* v_unused_3961_; 
v_unused_3961_ = lean_ctor_get(v_fst_3813_, 0);
lean_dec(v_unused_3961_);
v___x_3821_ = v_fst_3813_;
v_isShared_3822_ = v_isSharedCheck_3960_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_proc_3819_);
lean_dec(v_fst_3813_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3960_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v_declName_3823_; lean_object* v___x_3824_; lean_object* v___y_3826_; lean_object* v___x_3832_; uint8_t v___x_3833_; lean_object* v___y_3835_; 
v_declName_3823_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_3814_, 0);
lean_inc(v_declName_3823_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_3814_);
v___x_3824_ = lean_box(0);
v___x_3832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v___x_3833_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_3789_, v_declName_3823_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3858_; lean_object* v_options_3859_; lean_object* v_inheritedTraceOptions_3860_; uint8_t v_hasTrace_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; uint8_t v___x_3864_; 
v___x_3858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1));
v_options_3859_ = lean_ctor_get(v___y_3802_, 2);
v_inheritedTraceOptions_3860_ = lean_ctor_get(v___y_3802_, 13);
v_hasTrace_3861_ = lean_ctor_get_uint8(v_options_3859_, sizeof(void*)*1);
v___x_3862_ = lean_unsigned_to_nat(0u);
v___x_3863_ = lean_nat_dec_eq(v_snd_3815_, v___x_3862_);
v___x_3864_ = lean_bool_not(v_hasTrace_3861_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___y_3874_; lean_object* v___y_3875_; uint8_t v___y_3876_; lean_object* v_a_3877_; lean_object* v___y_3890_; lean_object* v___y_3891_; uint8_t v___y_3892_; lean_object* v_a_3893_; uint8_t v___y_3903_; uint8_t v_a_3953_; 
v___x_3865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2));
v___x_3866_ = l_Lean_privateToUserName(v_declName_3823_);
v___x_3867_ = lean_box(0);
v___x_3868_ = l_Lean_Name_replacePrefix(v___x_3866_, v___x_3858_, v___x_3867_);
v___x_3869_ = l_Lean_Name_replacePrefix(v___x_3868_, v___x_3865_, v___x_3867_);
lean_inc_ref(v_e_3790_);
v___f_3870_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed), 13, 2);
lean_closure_set(v___f_3870_, 0, v___x_3869_);
lean_closure_set(v___f_3870_, 1, v_e_3790_);
v___x_3871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6));
if (v_hasTrace_3861_ == 0)
{
v_a_3953_ = v_hasTrace_3861_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3957_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10);
v___x_3958_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3860_, v_options_3859_, v___x_3957_);
if (v___x_3958_ == 0)
{
v_a_3953_ = v___x_3958_;
goto v___jp_3952_;
}
else
{
v___y_3903_ = v___x_3958_;
goto v___jp_3902_;
}
}
v___jp_3873_:
{
lean_object* v___x_3878_; double v___x_3879_; double v___x_3880_; double v___x_3881_; double v___x_3882_; double v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3878_ = lean_io_mono_nanos_now();
v___x_3879_ = lean_float_of_nat(v___y_3874_);
v___x_3880_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7);
v___x_3881_ = lean_float_div(v___x_3879_, v___x_3880_);
v___x_3882_ = lean_float_of_nat(v___x_3878_);
v___x_3883_ = lean_float_div(v___x_3882_, v___x_3880_);
v___x_3884_ = lean_box_float(v___x_3881_);
v___x_3885_ = lean_box_float(v___x_3883_);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v_a_3877_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3871_, v___x_3810_, v___x_3872_, v_options_3859_, v___y_3876_, v___y_3875_, v___f_3870_, v___x_3887_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
v___y_3835_ = v___x_3888_;
goto v___jp_3834_;
}
v___jp_3889_:
{
lean_object* v___x_3894_; double v___x_3895_; double v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3894_ = lean_io_get_num_heartbeats();
v___x_3895_ = lean_float_of_nat(v___y_3890_);
v___x_3896_ = lean_float_of_nat(v___x_3894_);
v___x_3897_ = lean_box_float(v___x_3895_);
v___x_3898_ = lean_box_float(v___x_3896_);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3900_, 0, v_a_3893_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
v___x_3901_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3871_, v___x_3810_, v___x_3872_, v_options_3859_, v___y_3892_, v___y_3891_, v___f_3870_, v___x_3900_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
v___y_3835_ = v___x_3901_;
goto v___jp_3834_;
}
v___jp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3803_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v___x_3906_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3907_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3859_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = lean_io_mono_nanos_now();
lean_inc_ref(v_e_3790_);
v___x_3909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3863_, v_e_3790_, v_snd_3815_, v_proc_3819_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v_snd_3815_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set_tag(v___x_3912_, 1);
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
v___y_3874_ = v___x_3908_;
v___y_3875_ = v_a_3905_;
v___y_3876_ = v___y_3903_;
v_a_3877_ = v___x_3915_;
goto v___jp_3873_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
v_a_3918_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3909_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3909_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 0);
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
v___y_3874_ = v___x_3908_;
v___y_3875_ = v_a_3905_;
v___y_3876_ = v___y_3903_;
v_a_3877_ = v___x_3923_;
goto v___jp_3873_;
}
}
}
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_e_3790_);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3863_, v_e_3790_, v_snd_3815_, v_proc_3819_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v_snd_3815_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
lean_ctor_set_tag(v___x_3930_, 1);
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
v___y_3890_ = v___x_3926_;
v___y_3891_ = v_a_3905_;
v___y_3892_ = v___y_3903_;
v_a_3893_ = v___x_3933_;
goto v___jp_3889_;
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
v_a_3936_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3927_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3927_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
lean_ctor_set_tag(v___x_3938_, 0);
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
v___y_3890_ = v___x_3926_;
v___y_3891_ = v_a_3905_;
v___y_3892_ = v___y_3903_;
v_a_3893_ = v___x_3941_;
goto v___jp_3889_;
}
}
}
}
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec_ref(v___f_3870_);
lean_del_object(v___x_3821_);
lean_dec_ref(v_proc_3819_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec_ref(v_e_3790_);
v_a_3944_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3904_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3904_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
v___jp_3952_:
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3954_ = l_Lean_trace_profiler;
v___x_3955_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3859_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec_ref(v___f_3870_);
lean_inc_ref(v_e_3790_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3863_, v_e_3790_, v_snd_3815_, v_proc_3819_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v_snd_3815_);
v___y_3835_ = v___x_3956_;
goto v___jp_3834_;
}
else
{
v___y_3903_ = v_a_3953_;
goto v___jp_3902_;
}
}
}
else
{
lean_object* v___x_3959_; 
lean_dec(v_declName_3823_);
lean_inc_ref(v_e_3790_);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3863_, v_e_3790_, v_snd_3815_, v_proc_3819_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v_snd_3815_);
v___y_3835_ = v___x_3959_;
goto v___jp_3834_;
}
}
else
{
lean_dec(v_declName_3823_);
lean_del_object(v___x_3821_);
lean_dec_ref(v_proc_3819_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_3806_ = v___x_3832_;
goto v___jp_3805_;
}
v___jp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___y_3826_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 1, v___x_3824_);
lean_ctor_set(v___x_3817_, 0, v___x_3827_);
v___x_3829_ = v___x_3817_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3824_);
v___x_3829_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
return v___x_3830_;
}
}
v___jp_3834_:
{
if (lean_obj_tag(v___y_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3849_; 
v_a_3836_ = lean_ctor_get(v___y_3835_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___y_3835_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3838_ = v___y_3835_;
v_isShared_3839_ = v_isSharedCheck_3849_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___y_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3849_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
if (lean_obj_tag(v_a_3836_) == 1)
{
lean_del_object(v___x_3838_);
lean_del_object(v___x_3821_);
lean_dec_ref(v_e_3790_);
v___y_3826_ = v_a_3836_;
goto v___jp_3825_;
}
else
{
if (v___x_3833_ == 0)
{
lean_del_object(v___x_3817_);
if (lean_obj_tag(v_a_3836_) == 0)
{
uint8_t v_done_3840_; 
v_done_3840_ = lean_ctor_get_uint8(v_a_3836_, 0);
if (v_done_3840_ == 1)
{
uint8_t v_contextDependent_3841_; 
v_contextDependent_3841_ = lean_ctor_get_uint8(v_a_3836_, 1);
if (v_contextDependent_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_dec_ref(v_e_3790_);
v___x_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3842_, 0, v_a_3836_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v___x_3824_);
lean_ctor_set(v___x_3821_, 0, v___x_3842_);
v___x_3844_ = v___x_3821_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___x_3824_);
v___x_3844_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3846_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3844_);
v___x_3846_ = v___x_3838_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_dec_ref_known(v_a_3836_, 0);
lean_del_object(v___x_3838_);
lean_del_object(v___x_3821_);
v_a_3806_ = v___x_3832_;
goto v___jp_3805_;
}
}
else
{
lean_dec_ref_known(v_a_3836_, 0);
lean_del_object(v___x_3838_);
lean_del_object(v___x_3821_);
v_a_3806_ = v___x_3832_;
goto v___jp_3805_;
}
}
else
{
lean_del_object(v___x_3838_);
lean_dec(v_a_3836_);
lean_del_object(v___x_3821_);
v_a_3806_ = v___x_3832_;
goto v___jp_3805_;
}
}
else
{
lean_del_object(v___x_3838_);
lean_del_object(v___x_3821_);
lean_dec_ref(v_e_3790_);
v___y_3826_ = v_a_3836_;
goto v___jp_3825_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_del_object(v___x_3821_);
lean_del_object(v___x_3817_);
lean_dec_ref(v_e_3790_);
v_a_3850_ = lean_ctor_get(v___y_3835_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___y_3835_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___y_3835_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___y_3835_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
}
v___jp_3805_:
{
size_t v___x_3807_; size_t v___x_3808_; 
v___x_3807_ = ((size_t)1ULL);
v___x_3808_ = lean_usize_add(v_i_3793_, v___x_3807_);
lean_inc_ref(v_a_3806_);
v_i_3793_ = v___x_3808_;
v_b_3794_ = v_a_3806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object* v_erased_3964_, lean_object* v_e_3965_, lean_object* v_as_3966_, lean_object* v_sz_3967_, lean_object* v_i_3968_, lean_object* v_b_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
size_t v_sz_boxed_3980_; size_t v_i_boxed_3981_; lean_object* v_res_3982_; 
v_sz_boxed_3980_ = lean_unbox_usize(v_sz_3967_);
lean_dec(v_sz_3967_);
v_i_boxed_3981_ = lean_unbox_usize(v_i_3968_);
lean_dec(v_i_3968_);
v_res_3982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3964_, v_e_3965_, v_as_3966_, v_sz_boxed_3980_, v_i_boxed_3981_, v_b_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v_as_3966_);
lean_dec_ref(v_erased_3964_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object* v_tree_3985_, lean_object* v_erased_3986_, lean_object* v_e_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_candidates_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v_candidates_3998_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_tree_3985_, v_e_3987_);
v___x_3999_ = lean_array_get_size(v_candidates_3998_);
v___x_4000_ = lean_unsigned_to_nat(0u);
v___x_4001_ = lean_nat_dec_eq(v___x_3999_, v___x_4000_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; size_t v_sz_4003_; size_t v___x_4004_; lean_object* v___x_4005_; 
v___x_4002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v_sz_4003_ = lean_array_size(v_candidates_3998_);
v___x_4004_ = ((size_t)0ULL);
v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3986_, v_e_3987_, v_candidates_3998_, v_sz_4003_, v___x_4004_, v___x_4002_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_);
lean_dec_ref(v_candidates_3998_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4019_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4019_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4019_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v_fst_4010_; 
v_fst_4010_ = lean_ctor_get(v_a_4006_, 0);
lean_inc(v_fst_4010_);
lean_dec(v_a_4006_);
if (lean_obj_tag(v_fst_4010_) == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4011_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4011_, 0, v___x_4001_);
lean_ctor_set_uint8(v___x_4011_, 1, v___x_4001_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4011_);
v___x_4013_ = v___x_4008_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
else
{
lean_object* v_val_4015_; lean_object* v___x_4017_; 
v_val_4015_ = lean_ctor_get(v_fst_4010_, 0);
lean_inc(v_val_4015_);
lean_dec_ref_known(v_fst_4010_, 1);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v_val_4015_);
v___x_4017_ = v___x_4008_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_val_4015_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
v_a_4020_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4005_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4005_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
lean_dec_ref(v_candidates_3998_);
lean_dec_ref(v_e_3987_);
v___x_4028_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0));
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
return v___x_4029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object* v_tree_4030_, lean_object* v_erased_4031_, lean_object* v_e_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_4030_, v_erased_4031_, v_e_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_erased_4031_);
lean_dec_ref(v_tree_4030_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object* v_00_u03b1_4044_, lean_object* v_x_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_4045_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4057_, lean_object* v_x_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(v_00_u03b1_4057_, v_x_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object* v_oldTraces_4070_, lean_object* v_data_4071_, lean_object* v_ref_4072_, lean_object* v_msg_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_4070_, v_data_4071_, v_ref_4072_, v_msg_4073_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object* v_oldTraces_4085_, lean_object* v_data_4086_, lean_object* v_ref_4087_, lean_object* v_msg_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_oldTraces_4085_, v_data_4086_, v_ref_4087_, v_msg_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
return v_res_4099_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
