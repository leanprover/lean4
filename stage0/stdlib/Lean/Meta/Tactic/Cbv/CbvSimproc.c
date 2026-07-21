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
uint8_t l_Lean_initializing();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
uint8_t v___x_370_; 
v___x_370_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v___x_368_, v_k_364_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
v___x_371_ = lean_nat_dec_lt(v___x_366_, v___x_365_);
if (v___x_371_ == 0)
{
lean_dec(v_k_362_);
lean_dec_ref(v_v_361_);
return v_as_363_;
}
else
{
lean_object* v___x_372_; lean_object* v_xs_x27_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc(v___x_368_);
v___x_372_ = lean_box(0);
v_xs_x27_373_ = lean_array_fset(v_as_363_, v___x_366_, v___x_372_);
v___x_374_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_368_);
v___x_375_ = lean_array_fset(v_xs_x27_373_, v___x_366_, v___x_374_);
return v___x_375_;
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_sub(v___x_365_, v___x_376_);
v___x_378_ = lean_array_fget_borrowed(v_as_363_, v___x_377_);
v___x_379_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v___x_378_, v_k_364_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__1(v_k_364_, v___x_378_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_lt(v___x_377_, v___x_365_);
if (v___x_381_ == 0)
{
lean_dec(v___x_377_);
lean_dec(v_k_362_);
lean_dec_ref(v_v_361_);
return v_as_363_;
}
else
{
lean_object* v___x_382_; lean_object* v_xs_x27_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_inc(v___x_378_);
v___x_382_ = lean_box(0);
v_xs_x27_383_ = lean_array_fset(v_as_363_, v___x_377_, v___x_382_);
v___x_384_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_378_);
v___x_385_ = lean_array_fset(v_xs_x27_383_, v___x_377_, v___x_384_);
lean_dec(v___x_377_);
return v___x_385_;
}
}
else
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v_as_363_, v_k_364_, v___x_366_, v___x_377_);
return v___x_386_;
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v___x_377_);
v___x_387_ = lean_box(0);
v___x_388_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_387_);
v___x_389_ = lean_array_push(v_as_363_, v___x_388_);
return v___x_389_;
}
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_as_392_; lean_object* v___x_393_; 
v___x_390_ = lean_box(0);
v___x_391_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_390_);
v_as_392_ = lean_array_push(v_as_363_, v___x_391_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_366_, v_as_392_, v___x_365_);
return v___x_393_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
v___x_395_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__0(v_x_359_, v_keys_360_, v_v_361_, v_k_362_, v___x_394_);
v___x_396_ = lean_array_push(v_as_363_, v___x_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object* v_keys_397_, lean_object* v_v_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v_vs_401_; lean_object* v_children_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_419_; 
v_vs_401_ = lean_ctor_get(v_x_400_, 0);
v_children_402_ = lean_ctor_get(v_x_400_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_419_ == 0)
{
v___x_404_ = v_x_400_;
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_children_402_);
lean_inc(v_vs_401_);
lean_dec(v_x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_array_get_size(v_keys_397_);
v___x_407_ = lean_nat_dec_lt(v_x_399_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v_vs_401_, v_v_398_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_408_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_children_402_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v_k_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_c_415_; lean_object* v___x_417_; 
v_k_412_ = lean_array_fget_borrowed(v_keys_397_, v_x_399_);
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1));
lean_inc_n(v_k_412_, 2);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_k_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v_c_415_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_x_399_, v_keys_397_, v_v_398_, v_k_412_, v_children_402_, v___x_414_);
lean_dec_ref_known(v___x_414_, 2);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_c_415_);
v___x_417_ = v___x_404_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_vs_401_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_c_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(lean_object* v_x_420_, lean_object* v_keys_421_, lean_object* v_v_422_, lean_object* v_k_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_435_; 
v_snd_425_ = lean_ctor_get(v_x_424_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_x_424_, 0);
lean_dec(v_unused_436_);
v___x_427_ = v_x_424_;
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_dec(v_x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_c_431_; lean_object* v___x_433_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_x_420_, v___x_429_);
v_c_431_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_421_, v_v_422_, v___x_430_, v_snd_425_);
lean_dec(v___x_430_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v_c_431_);
lean_ctor_set(v___x_427_, 0, v_k_423_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_k_423_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_c_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2___boxed(lean_object* v_x_437_, lean_object* v_keys_438_, lean_object* v_v_439_, lean_object* v_k_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___lam__2(v_x_437_, v_keys_438_, v_v_439_, v_k_440_, v_x_441_);
lean_dec_ref(v_keys_438_);
lean_dec(v_x_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object* v_keys_443_, lean_object* v_v_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_443_, v_v_444_, v_x_445_, v_x_446_);
lean_dec(v_x_445_);
lean_dec_ref(v_keys_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg___boxed(lean_object* v_x_448_, lean_object* v_keys_449_, lean_object* v_v_450_, lean_object* v_k_451_, lean_object* v_as_452_, lean_object* v_k_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_448_, v_keys_449_, v_v_450_, v_k_451_, v_as_452_, v_k_453_, v_x_454_, v_x_455_);
lean_dec_ref(v_k_453_);
lean_dec_ref(v_keys_449_);
lean_dec(v_x_448_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9___boxed(lean_object* v_x_457_, lean_object* v_keys_458_, lean_object* v_v_459_, lean_object* v_k_460_, lean_object* v_as_461_, lean_object* v_k_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_x_457_, v_keys_458_, v_v_459_, v_k_460_, v_as_461_, v_k_462_);
lean_dec_ref(v_k_462_);
lean_dec_ref(v_keys_458_);
lean_dec(v_x_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(lean_object* v_keys_464_, lean_object* v_v_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_464_, v_v_465_, v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v_val_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_val_470_ = lean_ctor_get(v_x_466_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v_x_466_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_val_470_);
lean_dec(v_x_466_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_464_, v_v_465_, v___x_474_, v_val_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0___boxed(lean_object* v_keys_480_, lean_object* v_v_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_480_, v_v_481_, v_x_482_);
lean_dec_ref(v_keys_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_ks_488_; lean_object* v_vs_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v_ks_488_ = lean_ctor_get(v_x_484_, 0);
v_vs_489_ = lean_ctor_get(v_x_484_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_x_484_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_vs_489_);
lean_inc(v_ks_488_);
lean_dec(v_x_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_array_get_size(v_ks_488_);
v___x_494_ = lean_nat_dec_lt(v_x_485_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec(v_x_485_);
v___x_495_ = lean_array_push(v_ks_488_, v_x_486_);
v___x_496_ = lean_array_push(v_vs_489_, v_x_487_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_496_);
lean_ctor_set(v___x_491_, 0, v___x_495_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_object* v_k_x27_500_; uint8_t v___x_501_; 
v_k_x27_500_ = lean_array_fget_borrowed(v_ks_488_, v_x_485_);
v___x_501_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_486_, v_k_x27_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; 
if (v_isShared_492_ == 0)
{
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_ks_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_vs_489_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_x_485_, v___x_504_);
lean_dec(v_x_485_);
v_x_484_ = v___x_503_;
v_x_485_ = v___x_505_;
goto _start;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_array_fset(v_ks_488_, v_x_485_, v_x_486_);
v___x_509_ = lean_array_fset(v_vs_489_, v_x_485_, v_x_487_);
lean_dec(v_x_485_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_509_);
lean_ctor_set(v___x_491_, 0, v___x_508_);
v___x_511_ = v___x_491_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(lean_object* v_n_514_, lean_object* v_k_515_, lean_object* v_v_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(v_n_514_, v___x_517_, v_k_515_, v_v_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(lean_object* v_x_520_, size_t v_x_521_, size_t v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_es_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v_j_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_es_525_ = lean_ctor_get(v_x_520_, 0);
v___x_526_ = ((size_t)31ULL);
v___x_527_ = lean_usize_land(v_x_521_, v___x_526_);
v_j_528_ = lean_usize_to_nat(v___x_527_);
v___x_529_ = lean_array_get_size(v_es_525_);
v___x_530_ = lean_nat_dec_lt(v_j_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_j_528_);
lean_dec(v_x_524_);
lean_dec(v_x_523_);
return v_x_520_;
}
else
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_569_; 
lean_inc_ref(v_es_525_);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_x_520_, 0);
lean_dec(v_unused_570_);
v___x_532_ = v_x_520_;
v_isShared_533_ = v_isSharedCheck_569_;
goto v_resetjp_531_;
}
else
{
lean_dec(v_x_520_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_569_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_v_534_; lean_object* v___x_535_; lean_object* v_xs_x27_536_; lean_object* v___y_538_; 
v_v_534_ = lean_array_fget(v_es_525_, v_j_528_);
v___x_535_ = lean_box(0);
v_xs_x27_536_ = lean_array_fset(v_es_525_, v_j_528_, v___x_535_);
switch(lean_obj_tag(v_v_534_))
{
case 0:
{
lean_object* v_key_543_; lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_554_; 
v_key_543_ = lean_ctor_get(v_v_534_, 0);
v_val_544_ = lean_ctor_get(v_v_534_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_v_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_546_ = v_v_534_;
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_inc(v_key_543_);
lean_dec(v_v_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_523_, v_key_543_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_del_object(v___x_546_);
v___x_549_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_543_, v_val_544_, v_x_523_, v_x_524_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
v___y_538_ = v___x_550_;
goto v___jp_537_;
}
else
{
lean_object* v___x_552_; 
lean_dec(v_val_544_);
lean_dec(v_key_543_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v_x_524_);
lean_ctor_set(v___x_546_, 0, v_x_523_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_x_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_x_524_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v___y_538_ = v___x_552_;
goto v___jp_537_;
}
}
}
}
case 1:
{
lean_object* v_node_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v_node_555_ = lean_ctor_get(v_v_534_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_v_534_);
if (v_isSharedCheck_567_ == 0)
{
v___x_557_ = v_v_534_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_node_555_);
lean_dec(v_v_534_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_usize_shift_right(v_x_521_, v___x_559_);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_x_522_, v___x_561_);
v___x_563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_node_555_, v___x_560_, v___x_562_, v_x_523_, v_x_524_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_563_);
v___x_565_ = v___x_557_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v___y_538_ = v___x_565_;
goto v___jp_537_;
}
}
}
default: 
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_x_523_);
lean_ctor_set(v___x_568_, 1, v_x_524_);
v___y_538_ = v___x_568_;
goto v___jp_537_;
}
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = lean_array_fset(v_xs_x27_536_, v_j_528_, v___y_538_);
lean_dec(v_j_528_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_539_);
v___x_541_ = v___x_532_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
else
{
lean_object* v_ks_571_; lean_object* v_vs_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_592_; 
v_ks_571_ = lean_ctor_get(v_x_520_, 0);
v_vs_572_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_592_ == 0)
{
v___x_574_ = v_x_520_;
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_vs_572_);
lean_inc(v_ks_571_);
lean_dec(v_x_520_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_592_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_ks_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_vs_572_);
v___x_577_ = v_reuseFailAlloc_591_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v_newNode_578_; uint8_t v___y_580_; size_t v___x_586_; uint8_t v___x_587_; 
v_newNode_578_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(v___x_577_, v_x_523_, v_x_524_);
v___x_586_ = ((size_t)7ULL);
v___x_587_ = lean_usize_dec_le(v___x_586_, v_x_522_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_578_);
v___x_589_ = lean_unsigned_to_nat(4u);
v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
v___y_580_ = v___x_590_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___x_587_;
goto v___jp_579_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_object* v_ks_581_; lean_object* v_vs_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_ks_581_ = lean_ctor_get(v_newNode_578_, 0);
lean_inc_ref(v_ks_581_);
v_vs_582_ = lean_ctor_get(v_newNode_578_, 1);
lean_inc_ref(v_vs_582_);
lean_dec_ref(v_newNode_578_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___closed__0);
v___x_585_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_x_522_, v_ks_581_, v_vs_582_, v___x_583_, v___x_584_);
lean_dec_ref(v_vs_582_);
lean_dec_ref(v_ks_581_);
return v___x_585_;
}
else
{
return v_newNode_578_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(size_t v_depth_593_, lean_object* v_keys_594_, lean_object* v_vals_595_, lean_object* v_i_596_, lean_object* v_entries_597_){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_get_size(v_keys_594_);
v___x_599_ = lean_nat_dec_lt(v_i_596_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v_i_596_);
return v_entries_597_;
}
else
{
lean_object* v_k_600_; lean_object* v_v_601_; uint64_t v___x_602_; size_t v_h_603_; size_t v___x_604_; lean_object* v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v_h_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_k_600_ = lean_array_fget_borrowed(v_keys_594_, v_i_596_);
v_v_601_ = lean_array_fget_borrowed(v_vals_595_, v_i_596_);
v___x_602_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_600_);
v_h_603_ = lean_uint64_to_usize(v___x_602_);
v___x_604_ = ((size_t)5ULL);
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_sub(v_depth_593_, v___x_606_);
v___x_608_ = lean_usize_mul(v___x_604_, v___x_607_);
v_h_609_ = lean_usize_shift_right(v_h_603_, v___x_608_);
v___x_610_ = lean_nat_add(v_i_596_, v___x_605_);
lean_dec(v_i_596_);
lean_inc(v_v_601_);
lean_inc(v_k_600_);
v___x_611_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_entries_597_, v_h_609_, v_depth_593_, v_k_600_, v_v_601_);
v_i_596_ = v___x_610_;
v_entries_597_ = v___x_611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg___boxed(lean_object* v_depth_613_, lean_object* v_keys_614_, lean_object* v_vals_615_, lean_object* v_i_616_, lean_object* v_entries_617_){
_start:
{
size_t v_depth_boxed_618_; lean_object* v_res_619_; 
v_depth_boxed_618_ = lean_unbox_usize(v_depth_613_);
lean_dec(v_depth_613_);
v_res_619_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_depth_boxed_618_, v_keys_614_, v_vals_615_, v_i_616_, v_entries_617_);
lean_dec_ref(v_vals_615_);
lean_dec_ref(v_keys_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg___boxed(lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_2407__boxed_625_; size_t v_x_2408__boxed_626_; lean_object* v_res_627_; 
v_x_2407__boxed_625_ = lean_unbox_usize(v_x_621_);
lean_dec(v_x_621_);
v_x_2408__boxed_626_ = lean_unbox_usize(v_x_622_);
lean_dec(v_x_622_);
v_res_627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_x_620_, v_x_2407__boxed_625_, v_x_2408__boxed_626_, v_x_623_, v_x_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object* v_keys_628_, lean_object* v_v_629_, lean_object* v_x_630_, size_t v_x_631_, size_t v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_es_634_; size_t v___x_635_; size_t v___x_636_; lean_object* v_j_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_es_634_ = lean_ctor_get(v_x_630_, 0);
v___x_635_ = ((size_t)31ULL);
v___x_636_ = lean_usize_land(v_x_631_, v___x_635_);
v_j_637_ = lean_usize_to_nat(v___x_636_);
v___x_638_ = lean_array_get_size(v_es_634_);
v___x_639_ = lean_nat_dec_lt(v_j_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_dec(v_j_637_);
lean_dec(v_x_633_);
lean_dec_ref(v_v_629_);
return v_x_630_;
}
else
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_707_; 
lean_inc_ref(v_es_634_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_x_630_, 0);
lean_dec(v_unused_708_);
v___x_641_ = v_x_630_;
v_isShared_642_ = v_isSharedCheck_707_;
goto v_resetjp_640_;
}
else
{
lean_dec(v_x_630_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_707_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_v_643_; lean_object* v___x_644_; lean_object* v_xs_x27_645_; lean_object* v___y_647_; 
v_v_643_ = lean_array_fget(v_es_634_, v_j_637_);
v___x_644_ = lean_box(0);
v_xs_x27_645_ = lean_array_fset(v_es_634_, v_j_637_, v___x_644_);
switch(lean_obj_tag(v_v_643_))
{
case 0:
{
lean_object* v_key_652_; lean_object* v_val_653_; uint8_t v___x_654_; 
v_key_652_ = lean_ctor_get(v_v_643_, 0);
v_val_653_ = lean_ctor_get(v_v_643_, 1);
v___x_654_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_633_, v_key_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_box(0);
v___x_656_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_628_, v_v_629_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_dec(v_x_633_);
v___y_647_ = v_v_643_;
goto v___jp_646_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
lean_inc(v_val_653_);
lean_inc(v_key_652_);
lean_dec_ref_known(v_v_643_, 2);
v_val_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_652_, v_val_653_, v_x_633_, v_val_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_647_ = v___x_663_;
goto v___jp_646_;
}
}
}
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_676_; 
lean_inc(v_val_653_);
v_isSharedCheck_676_ = !lean_is_exclusive(v_v_643_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_677_ = lean_ctor_get(v_v_643_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_v_643_, 0);
lean_dec(v_unused_678_);
v___x_667_ = v_v_643_;
v_isShared_668_ = v_isSharedCheck_676_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_v_643_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_676_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_val_653_);
v___x_670_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_628_, v_v_629_, v___x_669_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_671_; 
lean_del_object(v___x_667_);
lean_dec(v_x_633_);
v___x_671_ = lean_box(2);
v___y_647_ = v___x_671_;
goto v___jp_646_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_674_; 
v_val_672_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v___x_670_, 1);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v_val_672_);
lean_ctor_set(v___x_667_, 0, v_x_633_);
v___x_674_ = v___x_667_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_x_633_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_val_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v___y_647_ = v___x_674_;
goto v___jp_646_;
}
}
}
}
}
case 1:
{
lean_object* v_node_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_702_; 
v_node_679_ = lean_ctor_get(v_v_643_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_v_643_);
if (v_isSharedCheck_702_ == 0)
{
v___x_681_ = v_v_643_;
v_isShared_682_ = v_isSharedCheck_702_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_node_679_);
lean_dec(v_v_643_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_702_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v_newNode_687_; lean_object* v___x_688_; 
v___x_683_ = ((size_t)5ULL);
v___x_684_ = lean_usize_shift_right(v_x_631_, v___x_683_);
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_add(v_x_632_, v___x_685_);
v_newNode_687_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_628_, v_v_629_, v_node_679_, v___x_684_, v___x_686_, v_x_633_);
lean_inc_ref(v_newNode_687_);
v___x_688_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_690_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_newNode_687_);
v___x_690_ = v___x_681_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_newNode_687_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_647_ = v___x_690_;
goto v___jp_646_;
}
}
else
{
lean_object* v_val_692_; lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_newNode_687_);
lean_del_object(v___x_681_);
v_val_692_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v___x_688_, 1);
v_fst_693_ = lean_ctor_get(v_val_692_, 0);
v_snd_694_ = lean_ctor_get(v_val_692_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_val_692_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v_val_692_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_dec(v_val_692_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_693_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v___y_647_ = v___x_699_;
goto v___jp_646_;
}
}
}
}
}
default: 
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_box(0);
v___x_704_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_628_, v_v_629_, v___x_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_dec(v_x_633_);
v___y_647_ = v_v_643_;
goto v___jp_646_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_706_; 
v_val_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_x_633_);
lean_ctor_set(v___x_706_, 1, v_val_705_);
v___y_647_ = v___x_706_;
goto v___jp_646_;
}
}
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_array_fset(v_xs_x27_645_, v_j_637_, v___y_647_);
lean_dec(v_j_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_648_);
v___x_650_ = v___x_641_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
else
{
lean_object* v_ks_709_; lean_object* v_vs_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_743_; 
v_ks_709_ = lean_ctor_get(v_x_630_, 0);
v_vs_710_ = lean_ctor_get(v_x_630_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_743_ == 0)
{
v___x_712_ = v_x_630_;
v_isShared_713_ = v_isSharedCheck_743_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_vs_710_);
lean_inc(v_ks_709_);
lean_dec(v_x_630_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_743_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; 
v___x_714_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__11(v_ks_709_, v_x_633_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_716_; 
if (v_isShared_713_ == 0)
{
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_ks_709_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_vs_710_);
v___x_716_ = v_reuseFailAlloc_721_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_box(0);
v___x_718_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_628_, v_v_629_, v___x_717_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_dec(v_x_633_);
return v___x_716_;
}
else
{
lean_object* v_val_719_; lean_object* v___x_720_; 
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v___x_716_, v_x_631_, v_x_632_, v_x_633_, v_val_719_);
return v___x_720_;
}
}
}
else
{
lean_object* v_val_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_742_; 
v_val_722_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_742_ == 0)
{
v___x_724_ = v___x_714_;
v_isShared_725_ = v_isSharedCheck_742_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_val_722_);
lean_dec(v___x_714_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_742_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_v_x27_726_; lean_object* v_keys_727_; lean_object* v_vals_728_; lean_object* v___x_730_; 
v_v_x27_726_ = lean_array_fget(v_vs_710_, v_val_722_);
lean_inc(v_val_722_);
v_keys_727_ = l_Array_eraseIdx___redArg(v_ks_709_, v_val_722_);
v_vals_728_ = l_Array_eraseIdx___redArg(v_vs_710_, v_val_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v_v_x27_726_);
v___x_730_ = v___x_724_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_v_x27_726_);
v___x_730_ = v_reuseFailAlloc_741_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_628_, v_v_629_, v___x_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_733_; 
lean_dec(v_x_633_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_vals_728_);
lean_ctor_set(v___x_712_, 0, v_keys_727_);
v___x_733_ = v___x_712_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_keys_727_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_vals_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
else
{
lean_object* v_val_735_; lean_object* v_keys_736_; lean_object* v_vals_737_; lean_object* v___x_739_; 
v_val_735_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_731_, 1);
v_keys_736_ = lean_array_push(v_keys_727_, v_x_633_);
v_vals_737_ = lean_array_push(v_vals_728_, v_val_735_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_vals_737_);
lean_ctor_set(v___x_712_, 0, v_keys_736_);
v___x_739_ = v___x_712_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_keys_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_vals_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___boxed(lean_object* v_keys_744_, lean_object* v_v_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
size_t v_x_2563__boxed_750_; size_t v_x_2564__boxed_751_; lean_object* v_res_752_; 
v_x_2563__boxed_750_ = lean_unbox_usize(v_x_747_);
lean_dec(v_x_747_);
v_x_2564__boxed_751_ = lean_unbox_usize(v_x_748_);
lean_dec(v_x_748_);
v_res_752_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_744_, v_v_745_, v_x_746_, v_x_2563__boxed_750_, v_x_2564__boxed_751_, v_x_749_);
lean_dec_ref(v_keys_744_);
return v_res_752_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object* v_msg_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0);
v___x_756_ = lean_panic_fn_borrowed(v___x_755_, v_msg_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2));
v___x_761_ = lean_unsigned_to_nat(23u);
v___x_762_ = lean_unsigned_to_nat(166u);
v___x_763_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1));
v___x_764_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0));
v___x_765_ = l_mkPanicMessageWithDecl(v___x_764_, v___x_763_, v___x_762_, v___x_761_, v___x_760_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object* v_d_766_, lean_object* v_keys_767_, lean_object* v_v_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_array_get_size(v_keys_767_);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_nat_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v_k_773_; uint64_t v___x_774_; size_t v_h_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_772_ = lean_box(0);
v_k_773_ = lean_array_get_borrowed(v___x_772_, v_keys_767_, v___x_770_);
v___x_774_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_773_);
v_h_775_ = lean_uint64_to_usize(v___x_774_);
v___x_776_ = ((size_t)1ULL);
lean_inc(v_k_773_);
v___x_777_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_767_, v_v_768_, v_d_766_, v_h_775_, v___x_776_, v_k_773_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v_v_768_);
lean_dec_ref(v_d_766_);
v___x_778_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
v___x_779_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object* v_d_780_, lean_object* v_keys_781_, lean_object* v_v_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_780_, v_keys_781_, v_v_782_);
lean_dec_ref(v_keys_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_ks_788_; lean_object* v_vs_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_813_; 
v_ks_788_ = lean_ctor_get(v_x_784_, 0);
v_vs_789_ = lean_ctor_get(v_x_784_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_813_ == 0)
{
v___x_791_ = v_x_784_;
v_isShared_792_ = v_isSharedCheck_813_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_vs_789_);
lean_inc(v_ks_788_);
lean_dec(v_x_784_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_813_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_ks_788_);
v___x_794_ = lean_nat_dec_lt(v_x_785_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v_x_785_);
v___x_795_ = lean_array_push(v_ks_788_, v_x_786_);
v___x_796_ = lean_array_push(v_vs_789_, v_x_787_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_796_);
lean_ctor_set(v___x_791_, 0, v___x_795_);
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
lean_object* v_k_x27_800_; uint8_t v___x_801_; 
v_k_x27_800_ = lean_array_fget_borrowed(v_ks_788_, v_x_785_);
v___x_801_ = lean_name_eq(v_x_786_, v_k_x27_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_803_; 
if (v_isShared_792_ == 0)
{
v___x_803_ = v___x_791_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_ks_788_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_vs_789_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_nat_add(v_x_785_, v___x_804_);
lean_dec(v_x_785_);
v_x_784_ = v___x_803_;
v_x_785_ = v___x_805_;
goto _start;
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = lean_array_fset(v_ks_788_, v_x_785_, v_x_786_);
v___x_809_ = lean_array_fset(v_vs_789_, v_x_785_, v_x_787_);
lean_dec(v_x_785_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_809_);
lean_ctor_set(v___x_791_, 0, v___x_808_);
v___x_811_ = v___x_791_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_814_, lean_object* v_k_815_, lean_object* v_v_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_814_, v___x_817_, v_k_815_, v_v_816_);
return v___x_818_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_819_; uint64_t v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(1723u);
v___x_820_ = lean_uint64_of_nat(v___x_819_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_822_, size_t v_x_823_, size_t v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v_es_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v_j_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_es_827_ = lean_ctor_get(v_x_822_, 0);
v___x_828_ = ((size_t)31ULL);
v___x_829_ = lean_usize_land(v_x_823_, v___x_828_);
v_j_830_ = lean_usize_to_nat(v___x_829_);
v___x_831_ = lean_array_get_size(v_es_827_);
v___x_832_ = lean_nat_dec_lt(v_j_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_dec(v_j_830_);
lean_dec(v_x_826_);
lean_dec(v_x_825_);
return v_x_822_;
}
else
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_871_; 
lean_inc_ref(v_es_827_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v_x_822_, 0);
lean_dec(v_unused_872_);
v___x_834_ = v_x_822_;
v_isShared_835_ = v_isSharedCheck_871_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_x_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_871_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_v_836_; lean_object* v___x_837_; lean_object* v_xs_x27_838_; lean_object* v___y_840_; 
v_v_836_ = lean_array_fget(v_es_827_, v_j_830_);
v___x_837_ = lean_box(0);
v_xs_x27_838_ = lean_array_fset(v_es_827_, v_j_830_, v___x_837_);
switch(lean_obj_tag(v_v_836_))
{
case 0:
{
lean_object* v_key_845_; lean_object* v_val_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_key_845_ = lean_ctor_get(v_v_836_, 0);
v_val_846_ = lean_ctor_get(v_v_836_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_v_836_);
if (v_isSharedCheck_856_ == 0)
{
v___x_848_ = v_v_836_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_val_846_);
lean_inc(v_key_845_);
lean_dec(v_v_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v___x_850_; 
v___x_850_ = lean_name_eq(v_x_825_, v_key_845_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_848_);
v___x_851_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_845_, v_val_846_, v_x_825_, v_x_826_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___y_840_ = v___x_852_;
goto v___jp_839_;
}
else
{
lean_object* v___x_854_; 
lean_dec(v_val_846_);
lean_dec(v_key_845_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_x_826_);
lean_ctor_set(v___x_848_, 0, v_x_825_);
v___x_854_ = v___x_848_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_x_825_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_x_826_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
v___y_840_ = v___x_854_;
goto v___jp_839_;
}
}
}
}
case 1:
{
lean_object* v_node_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_869_; 
v_node_857_ = lean_ctor_get(v_v_836_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_v_836_);
if (v_isSharedCheck_869_ == 0)
{
v___x_859_ = v_v_836_;
v_isShared_860_ = v_isSharedCheck_869_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_node_857_);
lean_dec(v_v_836_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_869_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
size_t v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_861_ = ((size_t)5ULL);
v___x_862_ = lean_usize_shift_right(v_x_823_, v___x_861_);
v___x_863_ = ((size_t)1ULL);
v___x_864_ = lean_usize_add(v_x_824_, v___x_863_);
v___x_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_857_, v___x_862_, v___x_864_, v_x_825_, v_x_826_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_865_);
v___x_867_ = v___x_859_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
v___y_840_ = v___x_867_;
goto v___jp_839_;
}
}
}
default: 
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_x_825_);
lean_ctor_set(v___x_870_, 1, v_x_826_);
v___y_840_ = v___x_870_;
goto v___jp_839_;
}
}
v___jp_839_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_array_fset(v_xs_x27_838_, v_j_830_, v___y_840_);
lean_dec(v_j_830_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_841_);
v___x_843_ = v___x_834_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
else
{
lean_object* v_ks_873_; lean_object* v_vs_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_894_; 
v_ks_873_ = lean_ctor_get(v_x_822_, 0);
v_vs_874_ = lean_ctor_get(v_x_822_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_894_ == 0)
{
v___x_876_ = v_x_822_;
v_isShared_877_ = v_isSharedCheck_894_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_vs_874_);
lean_inc(v_ks_873_);
lean_dec(v_x_822_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_894_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_ks_873_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_vs_874_);
v___x_879_ = v_reuseFailAlloc_893_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v_newNode_880_; uint8_t v___y_882_; size_t v___x_888_; uint8_t v___x_889_; 
v_newNode_880_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_879_, v_x_825_, v_x_826_);
v___x_888_ = ((size_t)7ULL);
v___x_889_ = lean_usize_dec_le(v___x_888_, v_x_824_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_880_);
v___x_891_ = lean_unsigned_to_nat(4u);
v___x_892_ = lean_nat_dec_lt(v___x_890_, v___x_891_);
lean_dec(v___x_890_);
v___y_882_ = v___x_892_;
goto v___jp_881_;
}
else
{
v___y_882_ = v___x_889_;
goto v___jp_881_;
}
v___jp_881_:
{
if (v___y_882_ == 0)
{
lean_object* v_ks_883_; lean_object* v_vs_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_ks_883_ = lean_ctor_get(v_newNode_880_, 0);
lean_inc_ref(v_ks_883_);
v_vs_884_ = lean_ctor_get(v_newNode_880_, 1);
lean_inc_ref(v_vs_884_);
lean_dec_ref(v_newNode_880_);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0);
v___x_887_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_824_, v_ks_883_, v_vs_884_, v___x_885_, v___x_886_);
lean_dec_ref(v_vs_884_);
lean_dec_ref(v_ks_883_);
return v___x_887_;
}
else
{
return v_newNode_880_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_895_, lean_object* v_keys_896_, lean_object* v_vals_897_, lean_object* v_i_898_, lean_object* v_entries_899_){
_start:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_array_get_size(v_keys_896_);
v___x_901_ = lean_nat_dec_lt(v_i_898_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec(v_i_898_);
return v_entries_899_;
}
else
{
lean_object* v_k_902_; lean_object* v_v_903_; uint64_t v___y_905_; 
v_k_902_ = lean_array_fget_borrowed(v_keys_896_, v_i_898_);
v_v_903_ = lean_array_fget_borrowed(v_vals_897_, v_i_898_);
if (lean_obj_tag(v_k_902_) == 0)
{
uint64_t v___x_916_; 
v___x_916_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_905_ = v___x_916_;
goto v___jp_904_;
}
else
{
uint64_t v_hash_917_; 
v_hash_917_ = lean_ctor_get_uint64(v_k_902_, sizeof(void*)*2);
v___y_905_ = v_hash_917_;
goto v___jp_904_;
}
v___jp_904_:
{
size_t v_h_906_; size_t v___x_907_; lean_object* v___x_908_; size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v_h_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_h_906_ = lean_uint64_to_usize(v___y_905_);
v___x_907_ = ((size_t)5ULL);
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_sub(v_depth_895_, v___x_909_);
v___x_911_ = lean_usize_mul(v___x_907_, v___x_910_);
v_h_912_ = lean_usize_shift_right(v_h_906_, v___x_911_);
v___x_913_ = lean_nat_add(v_i_898_, v___x_908_);
lean_dec(v_i_898_);
lean_inc(v_v_903_);
lean_inc(v_k_902_);
v___x_914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_899_, v_h_912_, v_depth_895_, v_k_902_, v_v_903_);
v_i_898_ = v___x_913_;
v_entries_899_ = v___x_914_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_918_, lean_object* v_keys_919_, lean_object* v_vals_920_, lean_object* v_i_921_, lean_object* v_entries_922_){
_start:
{
size_t v_depth_boxed_923_; lean_object* v_res_924_; 
v_depth_boxed_923_ = lean_unbox_usize(v_depth_918_);
lean_dec(v_depth_918_);
v_res_924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_923_, v_keys_919_, v_vals_920_, v_i_921_, v_entries_922_);
lean_dec_ref(v_vals_920_);
lean_dec_ref(v_keys_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
size_t v_x_2911__boxed_930_; size_t v_x_2912__boxed_931_; lean_object* v_res_932_; 
v_x_2911__boxed_930_ = lean_unbox_usize(v_x_926_);
lean_dec(v_x_926_);
v_x_2912__boxed_931_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_res_932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_925_, v_x_2911__boxed_930_, v_x_2912__boxed_931_, v_x_928_, v_x_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
uint64_t v___y_937_; 
if (lean_obj_tag(v_x_934_) == 0)
{
uint64_t v___x_941_; 
v___x_941_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_937_ = v___x_941_;
goto v___jp_936_;
}
else
{
uint64_t v_hash_942_; 
v_hash_942_ = lean_ctor_get_uint64(v_x_934_, sizeof(void*)*2);
v___y_937_ = v_hash_942_;
goto v___jp_936_;
}
v___jp_936_:
{
size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_uint64_to_usize(v___y_937_);
v___x_939_ = ((size_t)1ULL);
v___x_940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_933_, v___x_938_, v___x_939_, v_x_934_, v_x_935_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object* v_xs_943_, lean_object* v_v_944_, lean_object* v_i_945_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_array_get_size(v_xs_943_);
v___x_947_ = lean_nat_dec_lt(v_i_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_dec(v_i_945_);
v___x_948_ = lean_box(0);
return v___x_948_;
}
else
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_array_fget_borrowed(v_xs_943_, v_i_945_);
v___x_950_ = lean_name_eq(v___x_949_, v_v_944_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_add(v_i_945_, v___x_951_);
lean_dec(v_i_945_);
v_i_945_ = v___x_952_;
goto _start;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v_i_945_);
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_xs_955_, lean_object* v_v_956_, lean_object* v_i_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_955_, v_v_956_, v_i_957_);
lean_dec(v_v_956_);
lean_dec_ref(v_xs_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object* v_xs_959_, lean_object* v_v_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_959_, v_v_960_, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object* v_xs_963_, lean_object* v_v_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_963_, v_v_964_);
lean_dec(v_v_964_);
lean_dec_ref(v_xs_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object* v_x_966_, size_t v_x_967_, lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_es_969_; lean_object* v___x_970_; size_t v___x_971_; size_t v___x_972_; lean_object* v_j_973_; lean_object* v_entry_974_; 
v_es_969_ = lean_ctor_get(v_x_966_, 0);
v___x_970_ = lean_box(2);
v___x_971_ = ((size_t)31ULL);
v___x_972_ = lean_usize_land(v_x_967_, v___x_971_);
v_j_973_ = lean_usize_to_nat(v___x_972_);
v_entry_974_ = lean_array_get(v___x_970_, v_es_969_, v_j_973_);
switch(lean_obj_tag(v_entry_974_))
{
case 0:
{
lean_object* v_key_975_; uint8_t v___x_976_; 
v_key_975_ = lean_ctor_get(v_entry_974_, 0);
lean_inc(v_key_975_);
lean_dec_ref_known(v_entry_974_, 2);
v___x_976_ = lean_name_eq(v_x_968_, v_key_975_);
lean_dec(v_key_975_);
if (v___x_976_ == 0)
{
lean_dec(v_j_973_);
return v_x_966_;
}
else
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
lean_inc_ref(v_es_969_);
v_isSharedCheck_984_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; 
v_unused_985_ = lean_ctor_get(v_x_966_, 0);
lean_dec(v_unused_985_);
v___x_978_ = v_x_966_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_dec(v_x_966_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_array_set(v_es_969_, v_j_973_, v___x_970_);
lean_dec(v_j_973_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
case 1:
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1020_; 
lean_inc_ref(v_es_969_);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_x_966_, 0);
lean_dec(v_unused_1021_);
v___x_987_ = v_x_966_;
v_isShared_988_ = v_isSharedCheck_1020_;
goto v_resetjp_986_;
}
else
{
lean_dec(v_x_966_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1020_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_node_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1019_; 
v_node_989_ = lean_ctor_get(v_entry_974_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_entry_974_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_991_ = v_entry_974_;
v_isShared_992_ = v_isSharedCheck_1019_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_node_989_);
lean_dec(v_entry_974_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1019_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
size_t v___x_993_; lean_object* v_entries_994_; size_t v___x_995_; lean_object* v_newNode_996_; lean_object* v___x_997_; 
v___x_993_ = ((size_t)5ULL);
v_entries_994_ = lean_array_set(v_es_969_, v_j_973_, v___x_970_);
v___x_995_ = lean_usize_shift_right(v_x_967_, v___x_993_);
v_newNode_996_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_989_, v___x_995_, v_x_968_);
lean_inc_ref(v_newNode_996_);
v___x_997_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_999_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_newNode_996_);
v___x_999_ = v___x_991_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_newNode_996_);
v___x_999_ = v_reuseFailAlloc_1004_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_array_set(v_entries_994_, v_j_973_, v___x_999_);
lean_dec(v_j_973_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1000_);
v___x_1002_ = v___x_987_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v_val_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_newNode_996_);
lean_del_object(v___x_991_);
v_val_1005_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___x_997_, 1);
v_fst_1006_ = lean_ctor_get(v_val_1005_, 0);
v_snd_1007_ = lean_ctor_get(v_val_1005_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_val_1005_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1009_ = v_val_1005_;
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1007_);
lean_inc(v_fst_1006_);
lean_dec(v_val_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_snd_1007_);
v___x_1012_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_array_set(v_entries_994_, v_j_973_, v___x_1012_);
lean_dec(v_j_973_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1013_);
v___x_1015_ = v___x_987_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_973_);
return v_x_966_;
}
}
}
else
{
lean_object* v_ks_1022_; lean_object* v_vs_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
v_ks_1022_ = lean_ctor_get(v_x_966_, 0);
v_vs_1023_ = lean_ctor_get(v_x_966_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v_x_966_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_vs_1023_);
lean_inc(v_ks_1022_);
lean_dec(v_x_966_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_1022_, v_x_968_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1029_; 
if (v_isShared_1026_ == 0)
{
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_ks_1022_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_vs_1023_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
lean_object* v_val_1031_; lean_object* v_keys_x27_1032_; lean_object* v_vals_x27_1033_; lean_object* v___x_1035_; 
v_val_1031_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_n(v_val_1031_, 2);
lean_dec_ref_known(v___x_1027_, 1);
v_keys_x27_1032_ = l_Array_eraseIdx___redArg(v_ks_1022_, v_val_1031_);
v_vals_x27_1033_ = l_Array_eraseIdx___redArg(v_vs_1023_, v_val_1031_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v_vals_x27_1033_);
lean_ctor_set(v___x_1025_, 0, v_keys_x27_1032_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_keys_x27_1032_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_vals_x27_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
size_t v_x_3114__boxed_1041_; lean_object* v_res_1042_; 
v_x_3114__boxed_1041_ = lean_unbox_usize(v_x_1039_);
lean_dec(v_x_1039_);
v_res_1042_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1038_, v_x_3114__boxed_1041_, v_x_1040_);
lean_dec(v_x_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
uint64_t v___y_1046_; 
if (lean_obj_tag(v_x_1044_) == 0)
{
uint64_t v___x_1049_; 
v___x_1049_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1046_ = v___x_1049_;
goto v___jp_1045_;
}
else
{
uint64_t v_hash_1050_; 
v_hash_1050_ = lean_ctor_get_uint64(v_x_1044_, sizeof(void*)*2);
v___y_1046_ = v_hash_1050_;
goto v___jp_1045_;
}
v___jp_1045_:
{
size_t v_h_1047_; lean_object* v___x_1048_; 
v_h_1047_ = lean_uint64_to_usize(v___y_1046_);
v___x_1048_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1043_, v_h_1047_, v_x_1044_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1051_, v_x_1052_);
lean_dec(v_x_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object* v_s_1054_, lean_object* v_keys_1055_, lean_object* v_declName_1056_, uint8_t v_phase_1057_, lean_object* v_proc_1058_){
_start:
{
lean_object* v_pre_1059_; lean_object* v_eval_1060_; lean_object* v_post_1061_; lean_object* v_simprocNames_1062_; lean_object* v_erased_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1084_; 
v_pre_1059_ = lean_ctor_get(v_s_1054_, 0);
v_eval_1060_ = lean_ctor_get(v_s_1054_, 1);
v_post_1061_ = lean_ctor_get(v_s_1054_, 2);
v_simprocNames_1062_ = lean_ctor_get(v_s_1054_, 3);
v_erased_1063_ = lean_ctor_get(v_s_1054_, 4);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_s_1054_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1065_ = v_s_1054_;
v_isShared_1066_ = v_isSharedCheck_1084_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_erased_1063_);
lean_inc(v_simprocNames_1062_);
lean_inc(v_post_1061_);
lean_inc(v_eval_1060_);
lean_inc(v_pre_1059_);
lean_dec(v_s_1054_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1084_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v_entry_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_inc_ref(v_keys_1055_);
lean_inc_n(v_declName_1056_, 2);
v___x_1067_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1067_, 0, v_declName_1056_);
lean_ctor_set(v___x_1067_, 1, v_keys_1055_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*2, v_phase_1057_);
v_entry_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_entry_1068_, 0, v___x_1067_);
lean_ctor_set(v_entry_1068_, 1, v_proc_1058_);
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_1062_, v_declName_1056_, v___x_1069_);
v___x_1071_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_1063_, v_declName_1056_);
lean_dec(v_declName_1056_);
switch(v_phase_1057_)
{
case 0:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_1059_, v_keys_1055_, v_entry_1068_);
lean_dec_ref(v_keys_1055_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1071_);
lean_ctor_set(v___x_1065_, 3, v___x_1070_);
lean_ctor_set(v___x_1065_, 0, v___x_1072_);
v___x_1074_ = v___x_1065_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_eval_1060_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_post_1061_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v___x_1071_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
case 1:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_1060_, v_keys_1055_, v_entry_1068_);
lean_dec_ref(v_keys_1055_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1071_);
lean_ctor_set(v___x_1065_, 3, v___x_1070_);
lean_ctor_set(v___x_1065_, 1, v___x_1076_);
v___x_1078_ = v___x_1065_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_pre_1059_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_post_1061_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___x_1071_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
default: 
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_1061_, v_keys_1055_, v_entry_1068_);
lean_dec_ref(v_keys_1055_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1071_);
lean_ctor_set(v___x_1065_, 3, v___x_1070_);
lean_ctor_set(v___x_1065_, 2, v___x_1080_);
v___x_1082_ = v___x_1065_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_pre_1059_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_eval_1060_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v___x_1071_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object* v_s_1085_, lean_object* v_keys_1086_, lean_object* v_declName_1087_, lean_object* v_phase_1088_, lean_object* v_proc_1089_){
_start:
{
uint8_t v_phase_boxed_1090_; lean_object* v_res_1091_; 
v_phase_boxed_1090_ = lean_unbox(v_phase_1088_);
v_res_1091_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_1085_, v_keys_1086_, v_declName_1087_, v_phase_boxed_1090_, v_proc_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object* v_00_u03b2_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_1093_, v_x_1094_, v_x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1098_, v_x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object* v_00_u03b2_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(v_00_u03b2_1101_, v_x_1102_, v_x_1103_);
lean_dec(v_x_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, size_t v_x_1107_, size_t v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1106_, v_x_1107_, v_x_1108_, v_x_1109_, v_x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
size_t v_x_3323__boxed_1118_; size_t v_x_3324__boxed_1119_; lean_object* v_res_1120_; 
v_x_3323__boxed_1118_ = lean_unbox_usize(v_x_1114_);
lean_dec(v_x_1114_);
v_x_3324__boxed_1119_ = lean_unbox_usize(v_x_1115_);
lean_dec(v_x_1115_);
v_res_1120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_1112_, v_x_1113_, v_x_3323__boxed_1118_, v_x_3324__boxed_1119_, v_x_1116_, v_x_1117_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, size_t v_x_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1122_, v_x_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
size_t v_x_3340__boxed_1130_; lean_object* v_res_1131_; 
v_x_3340__boxed_1130_ = lean_unbox_usize(v_x_1128_);
lean_dec(v_x_1128_);
v_res_1131_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_1126_, v_x_1127_, v_x_3340__boxed_1130_, v_x_1129_);
lean_dec(v_x_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1132_, lean_object* v_n_1133_, lean_object* v_k_1134_, lean_object* v_v_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_1133_, v_k_1134_, v_v_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1137_, size_t v_depth_1138_, lean_object* v_keys_1139_, lean_object* v_vals_1140_, lean_object* v_heq_1141_, lean_object* v_i_1142_, lean_object* v_entries_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_1138_, v_keys_1139_, v_vals_1140_, v_i_1142_, v_entries_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1145_, lean_object* v_depth_1146_, lean_object* v_keys_1147_, lean_object* v_vals_1148_, lean_object* v_heq_1149_, lean_object* v_i_1150_, lean_object* v_entries_1151_){
_start:
{
size_t v_depth_boxed_1152_; lean_object* v_res_1153_; 
v_depth_boxed_1152_ = lean_unbox_usize(v_depth_1146_);
lean_dec(v_depth_1146_);
v_res_1153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_1145_, v_depth_boxed_1152_, v_keys_1147_, v_vals_1148_, v_heq_1149_, v_i_1150_, v_entries_1151_);
lean_dec_ref(v_vals_1148_);
lean_dec_ref(v_keys_1147_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(lean_object* v_00_u03b2_1154_, lean_object* v_x_1155_, size_t v_x_1156_, size_t v_x_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___redArg(v_x_1155_, v_x_1156_, v_x_1157_, v_x_1158_, v_x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
size_t v_x_3355__boxed_1167_; size_t v_x_3356__boxed_1168_; lean_object* v_res_1169_; 
v_x_3355__boxed_1167_ = lean_unbox_usize(v_x_1163_);
lean_dec(v_x_1163_);
v_x_3356__boxed_1168_ = lean_unbox_usize(v_x_1164_);
lean_dec(v_x_1164_);
v_res_1169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(v_00_u03b2_1161_, v_x_1162_, v_x_3355__boxed_1167_, v_x_3356__boxed_1168_, v_x_1165_, v_x_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1171_, v_x_1172_, v_x_1173_, v_x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(lean_object* v_x_1176_, lean_object* v_keys_1177_, lean_object* v_v_1178_, lean_object* v_k_1179_, lean_object* v_as_1180_, lean_object* v_k_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___redArg(v_x_1176_, v_keys_1177_, v_v_1178_, v_k_1179_, v_as_1180_, v_k_1181_, v_x_1182_, v_x_1183_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14___boxed(lean_object* v_x_1187_, lean_object* v_keys_1188_, lean_object* v_v_1189_, lean_object* v_k_1190_, lean_object* v_as_1191_, lean_object* v_k_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(v_x_1187_, v_keys_1188_, v_v_1189_, v_k_1190_, v_as_1191_, v_k_1192_, v_x_1193_, v_x_1194_, v_x_1195_, v_x_1196_);
lean_dec_ref(v_k_1192_);
lean_dec_ref(v_keys_1188_);
lean_dec(v_x_1187_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(lean_object* v_00_u03b2_1198_, lean_object* v_n_1199_, lean_object* v_k_1200_, lean_object* v_v_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___redArg(v_n_1199_, v_k_1200_, v_v_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(lean_object* v_00_u03b2_1203_, size_t v_depth_1204_, lean_object* v_keys_1205_, lean_object* v_vals_1206_, lean_object* v_heq_1207_, lean_object* v_i_1208_, lean_object* v_entries_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___redArg(v_depth_1204_, v_keys_1205_, v_vals_1206_, v_i_1208_, v_entries_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20___boxed(lean_object* v_00_u03b2_1211_, lean_object* v_depth_1212_, lean_object* v_keys_1213_, lean_object* v_vals_1214_, lean_object* v_heq_1215_, lean_object* v_i_1216_, lean_object* v_entries_1217_){
_start:
{
size_t v_depth_boxed_1218_; lean_object* v_res_1219_; 
v_depth_boxed_1218_ = lean_unbox_usize(v_depth_1212_);
lean_dec(v_depth_1212_);
v_res_1219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__20(v_00_u03b2_1211_, v_depth_boxed_1218_, v_keys_1213_, v_vals_1214_, v_heq_1215_, v_i_1216_, v_entries_1217_);
lean_dec_ref(v_vals_1214_);
lean_dec_ref(v_keys_1213_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20(lean_object* v_00_u03b2_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19_spec__20___redArg(v_x_1221_, v_x_1222_, v_x_1223_, v_x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object* v_s_1226_, lean_object* v_declName_1227_){
_start:
{
lean_object* v_pre_1228_; lean_object* v_eval_1229_; lean_object* v_post_1230_; lean_object* v_simprocNames_1231_; lean_object* v_erased_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1242_; 
v_pre_1228_ = lean_ctor_get(v_s_1226_, 0);
v_eval_1229_ = lean_ctor_get(v_s_1226_, 1);
v_post_1230_ = lean_ctor_get(v_s_1226_, 2);
v_simprocNames_1231_ = lean_ctor_get(v_s_1226_, 3);
v_erased_1232_ = lean_ctor_get(v_s_1226_, 4);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_s_1226_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1234_ = v_s_1226_;
v_isShared_1235_ = v_isSharedCheck_1242_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_erased_1232_);
lean_inc(v_simprocNames_1231_);
lean_inc(v_post_1230_);
lean_inc(v_eval_1229_);
lean_inc(v_pre_1228_);
lean_dec(v_s_1226_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1242_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1236_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_1231_, v_declName_1227_);
v___x_1237_ = lean_box(0);
v___x_1238_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_1232_, v_declName_1227_, v___x_1237_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 4, v___x_1238_);
lean_ctor_set(v___x_1234_, 3, v___x_1236_);
v___x_1240_ = v___x_1234_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_pre_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_eval_1229_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_post_1230_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_unsigned_to_nat(16u);
v___x_1245_ = lean_mk_array(v___x_1244_, v___x_1243_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___x_1246_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default(void){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
return v___x_1251_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs(void){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1255_ = lean_st_mk_ref(v___x_1254_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
return v_res_1258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object* v_a_1259_, lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = 0;
return v___x_1261_;
}
else
{
lean_object* v_key_1262_; lean_object* v_tail_1263_; uint8_t v___x_1264_; 
v_key_1262_ = lean_ctor_get(v_x_1260_, 0);
v_tail_1263_ = lean_ctor_get(v_x_1260_, 2);
v___x_1264_ = lean_name_eq(v_key_1262_, v_a_1259_);
if (v___x_1264_ == 0)
{
v_x_1260_ = v_tail_1263_;
goto _start;
}
else
{
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_1266_, lean_object* v_x_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1266_, v_x_1267_);
lean_dec(v_x_1267_);
lean_dec(v_a_1266_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object* v_m_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_buckets_1272_; lean_object* v___x_1273_; uint64_t v___y_1275_; 
v_buckets_1272_ = lean_ctor_get(v_m_1270_, 1);
v___x_1273_ = lean_array_get_size(v_buckets_1272_);
if (lean_obj_tag(v_a_1271_) == 0)
{
uint64_t v___x_1289_; 
v___x_1289_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1275_ = v___x_1289_;
goto v___jp_1274_;
}
else
{
uint64_t v_hash_1290_; 
v_hash_1290_ = lean_ctor_get_uint64(v_a_1271_, sizeof(void*)*2);
v___y_1275_ = v_hash_1290_;
goto v___jp_1274_;
}
v___jp_1274_:
{
uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v_fold_1278_; uint64_t v___x_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1276_ = 32ULL;
v___x_1277_ = lean_uint64_shift_right(v___y_1275_, v___x_1276_);
v_fold_1278_ = lean_uint64_xor(v___y_1275_, v___x_1277_);
v___x_1279_ = 16ULL;
v___x_1280_ = lean_uint64_shift_right(v_fold_1278_, v___x_1279_);
v___x_1281_ = lean_uint64_xor(v_fold_1278_, v___x_1280_);
v___x_1282_ = lean_uint64_to_usize(v___x_1281_);
v___x_1283_ = lean_usize_of_nat(v___x_1273_);
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = lean_usize_sub(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_usize_land(v___x_1282_, v___x_1285_);
v___x_1287_ = lean_array_uget_borrowed(v_buckets_1272_, v___x_1286_);
v___x_1288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1271_, v___x_1287_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object* v_m_1291_, lean_object* v_a_1292_){
_start:
{
uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_res_1293_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_m_1291_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v_x_1297_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_dec(v_b_1296_);
lean_dec(v_a_1295_);
return v_x_1297_;
}
else
{
lean_object* v_key_1298_; lean_object* v_value_1299_; lean_object* v_tail_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1312_; 
v_key_1298_ = lean_ctor_get(v_x_1297_, 0);
v_value_1299_ = lean_ctor_get(v_x_1297_, 1);
v_tail_1300_ = lean_ctor_get(v_x_1297_, 2);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1302_ = v_x_1297_;
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_tail_1300_);
lean_inc(v_value_1299_);
lean_inc(v_key_1298_);
lean_dec(v_x_1297_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_name_eq(v_key_1298_, v_a_1295_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1295_, v_b_1296_, v_tail_1300_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v___x_1305_);
v___x_1307_ = v___x_1302_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_key_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_value_1299_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v___x_1310_; 
lean_dec(v_value_1299_);
lean_dec(v_key_1298_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 1, v_b_1296_);
lean_ctor_set(v___x_1302_, 0, v_a_1295_);
v___x_1310_ = v___x_1302_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1295_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_b_1296_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_tail_1300_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
return v_x_1313_;
}
else
{
lean_object* v_key_1315_; lean_object* v_value_1316_; lean_object* v_tail_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1343_; 
v_key_1315_ = lean_ctor_get(v_x_1314_, 0);
v_value_1316_ = lean_ctor_get(v_x_1314_, 1);
v_tail_1317_ = lean_ctor_get(v_x_1314_, 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1314_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1319_ = v_x_1314_;
v_isShared_1320_ = v_isSharedCheck_1343_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_tail_1317_);
lean_inc(v_value_1316_);
lean_inc(v_key_1315_);
lean_dec(v_x_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1343_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; uint64_t v___y_1323_; 
v___x_1321_ = lean_array_get_size(v_x_1313_);
if (lean_obj_tag(v_key_1315_) == 0)
{
uint64_t v___x_1341_; 
v___x_1341_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1323_ = v___x_1341_;
goto v___jp_1322_;
}
else
{
uint64_t v_hash_1342_; 
v_hash_1342_ = lean_ctor_get_uint64(v_key_1315_, sizeof(void*)*2);
v___y_1323_ = v_hash_1342_;
goto v___jp_1322_;
}
v___jp_1322_:
{
uint64_t v___x_1324_; uint64_t v___x_1325_; uint64_t v_fold_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1324_ = 32ULL;
v___x_1325_ = lean_uint64_shift_right(v___y_1323_, v___x_1324_);
v_fold_1326_ = lean_uint64_xor(v___y_1323_, v___x_1325_);
v___x_1327_ = 16ULL;
v___x_1328_ = lean_uint64_shift_right(v_fold_1326_, v___x_1327_);
v___x_1329_ = lean_uint64_xor(v_fold_1326_, v___x_1328_);
v___x_1330_ = lean_uint64_to_usize(v___x_1329_);
v___x_1331_ = lean_usize_of_nat(v___x_1321_);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_sub(v___x_1331_, v___x_1332_);
v___x_1334_ = lean_usize_land(v___x_1330_, v___x_1333_);
v___x_1335_ = lean_array_uget_borrowed(v_x_1313_, v___x_1334_);
lean_inc(v___x_1335_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 2, v___x_1335_);
v___x_1337_ = v___x_1319_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_key_1315_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_value_1316_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_array_uset(v_x_1313_, v___x_1334_, v___x_1337_);
v_x_1313_ = v___x_1338_;
v_x_1314_ = v_tail_1317_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1344_, lean_object* v_source_1345_, lean_object* v_target_1346_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = lean_array_get_size(v_source_1345_);
v___x_1348_ = lean_nat_dec_lt(v_i_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v_source_1345_);
lean_dec(v_i_1344_);
return v_target_1346_;
}
else
{
lean_object* v_es_1349_; lean_object* v___x_1350_; lean_object* v_source_1351_; lean_object* v_target_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_es_1349_ = lean_array_fget(v_source_1345_, v_i_1344_);
v___x_1350_ = lean_box(0);
v_source_1351_ = lean_array_fset(v_source_1345_, v_i_1344_, v___x_1350_);
v_target_1352_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1346_, v_es_1349_);
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = lean_nat_add(v_i_1344_, v___x_1353_);
lean_dec(v_i_1344_);
v_i_1344_ = v___x_1354_;
v_source_1345_ = v_source_1351_;
v_target_1346_ = v_target_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object* v_data_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_nbuckets_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1357_ = lean_array_get_size(v_data_1356_);
v___x_1358_ = lean_unsigned_to_nat(2u);
v_nbuckets_1359_ = lean_nat_mul(v___x_1357_, v___x_1358_);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_mk_array(v_nbuckets_1359_, v___x_1361_);
v___x_1363_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v___x_1360_, v_data_1356_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object* v_m_1364_, lean_object* v_a_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v_size_1367_; lean_object* v_buckets_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1414_; 
v_size_1367_ = lean_ctor_get(v_m_1364_, 0);
v_buckets_1368_ = lean_ctor_get(v_m_1364_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_m_1364_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1370_ = v_m_1364_;
v_isShared_1371_ = v_isSharedCheck_1414_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_buckets_1368_);
lean_inc(v_size_1367_);
lean_dec(v_m_1364_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1414_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; uint64_t v___y_1374_; 
v___x_1372_ = lean_array_get_size(v_buckets_1368_);
if (lean_obj_tag(v_a_1365_) == 0)
{
uint64_t v___x_1412_; 
v___x_1412_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1374_ = v___x_1412_;
goto v___jp_1373_;
}
else
{
uint64_t v_hash_1413_; 
v_hash_1413_ = lean_ctor_get_uint64(v_a_1365_, sizeof(void*)*2);
v___y_1374_ = v_hash_1413_;
goto v___jp_1373_;
}
v___jp_1373_:
{
uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v_fold_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; uint64_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; lean_object* v_bkt_1386_; uint8_t v___x_1387_; 
v___x_1375_ = 32ULL;
v___x_1376_ = lean_uint64_shift_right(v___y_1374_, v___x_1375_);
v_fold_1377_ = lean_uint64_xor(v___y_1374_, v___x_1376_);
v___x_1378_ = 16ULL;
v___x_1379_ = lean_uint64_shift_right(v_fold_1377_, v___x_1378_);
v___x_1380_ = lean_uint64_xor(v_fold_1377_, v___x_1379_);
v___x_1381_ = lean_uint64_to_usize(v___x_1380_);
v___x_1382_ = lean_usize_of_nat(v___x_1372_);
v___x_1383_ = ((size_t)1ULL);
v___x_1384_ = lean_usize_sub(v___x_1382_, v___x_1383_);
v___x_1385_ = lean_usize_land(v___x_1381_, v___x_1384_);
v_bkt_1386_ = lean_array_uget_borrowed(v_buckets_1368_, v___x_1385_);
v___x_1387_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1365_, v_bkt_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v_size_x27_1389_; lean_object* v___x_1390_; lean_object* v_buckets_x27_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v_size_x27_1389_ = lean_nat_add(v_size_1367_, v___x_1388_);
lean_dec(v_size_1367_);
lean_inc(v_bkt_1386_);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1365_);
lean_ctor_set(v___x_1390_, 1, v_b_1366_);
lean_ctor_set(v___x_1390_, 2, v_bkt_1386_);
v_buckets_x27_1391_ = lean_array_uset(v_buckets_1368_, v___x_1385_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = lean_nat_mul(v_size_x27_1389_, v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(3u);
v___x_1395_ = lean_nat_div(v___x_1393_, v___x_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_array_get_size(v_buckets_x27_1391_);
v___x_1397_ = lean_nat_dec_le(v___x_1395_, v___x_1396_);
lean_dec(v___x_1395_);
if (v___x_1397_ == 0)
{
lean_object* v_val_1398_; lean_object* v___x_1400_; 
v_val_1398_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_buckets_x27_1391_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_val_1398_);
lean_ctor_set(v___x_1370_, 0, v_size_x27_1389_);
v___x_1400_ = v___x_1370_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_size_x27_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_val_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1403_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_buckets_x27_1391_);
lean_ctor_set(v___x_1370_, 0, v_size_x27_1389_);
v___x_1403_ = v___x_1370_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_size_x27_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_buckets_x27_1391_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v_buckets_x27_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_inc(v_bkt_1386_);
v___x_1405_ = lean_box(0);
v_buckets_x27_1406_ = lean_array_uset(v_buckets_1368_, v___x_1385_, v___x_1405_);
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1365_, v_b_1366_, v_bkt_1386_);
v___x_1408_ = lean_array_uset(v_buckets_x27_1406_, v___x_1385_, v___x_1407_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1408_);
v___x_1410_ = v___x_1370_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_size_1367_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0));
v___x_1417_ = lean_mk_io_user_error(v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object* v_declName_1420_, lean_object* v_keys_1421_, lean_object* v_proc_1422_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Lean_initializing();
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_proc_1422_);
lean_dec_ref(v_keys_1421_);
lean_dec(v_declName_1420_);
v___x_1425_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_keys_1429_; uint8_t v___x_1430_; 
v___x_1427_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_1428_ = lean_st_ref_get(v___x_1427_);
v_keys_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc_ref(v_keys_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_1429_, v_declName_1420_);
lean_dec_ref(v_keys_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v_keys_1432_; lean_object* v_procs_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1444_; 
v___x_1431_ = lean_st_ref_take(v___x_1427_);
v_keys_1432_ = lean_ctor_get(v___x_1431_, 0);
v_procs_1433_ = lean_ctor_get(v___x_1431_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1435_ = v___x_1431_;
v_isShared_1436_ = v_isSharedCheck_1444_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_procs_1433_);
lean_inc(v_keys_1432_);
lean_dec(v___x_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1444_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_inc(v_declName_1420_);
v___x_1437_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_1432_, v_declName_1420_, v_keys_1421_);
v___x_1438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_1433_, v_declName_1420_, v_proc_1422_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1438_);
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_st_ref_set(v___x_1427_, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_proc_1422_);
lean_dec_ref(v_keys_1421_);
v___x_1445_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2));
v___x_1446_ = l_Lean_privateToUserName(v_declName_1420_);
v___x_1447_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1446_, v___x_1430_);
v___x_1448_ = lean_string_append(v___x_1445_, v___x_1447_);
lean_dec_ref(v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
v___x_1451_ = lean_mk_io_user_error(v___x_1450_);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object* v_declName_1453_, lean_object* v_keys_1454_, lean_object* v_proc_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1453_, v_keys_1454_, v_proc_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object* v_00_u03b2_1458_, lean_object* v_m_1459_, lean_object* v_a_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1459_, v_a_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_m_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_res_1465_; lean_object* v_r_1466_; 
v_res_1465_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_1462_, v_m_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_m_1463_);
v_r_1466_ = lean_box(v_res_1465_);
return v_r_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1468_, v_a_1469_, v_b_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object* v_00_u03b2_1472_, lean_object* v_a_1473_, lean_object* v_x_1474_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1473_, v_x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_){
_start:
{
uint8_t v_res_1479_; lean_object* v_r_1480_; 
v_res_1479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_1476_, v_a_1477_, v_x_1478_);
lean_dec(v_x_1478_);
lean_dec(v_a_1477_);
v_r_1480_ = lean_box(v_res_1479_);
return v_r_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object* v_00_u03b2_1481_, lean_object* v_data_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_data_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object* v_00_u03b2_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_, lean_object* v_x_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1485_, v_b_1486_, v_x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1489_, lean_object* v_i_1490_, lean_object* v_source_1491_, lean_object* v_target_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v_i_1490_, v_source_1491_, v_target_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1495_, v_x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object* v_d_u2081_1505_, lean_object* v_d_u2082_1506_){
_start:
{
lean_object* v_declName_1507_; lean_object* v_declName_1508_; uint8_t v___x_1509_; 
v_declName_1507_ = lean_ctor_get(v_d_u2081_1505_, 0);
v_declName_1508_ = lean_ctor_get(v_d_u2082_1506_, 0);
v___x_1509_ = l_Lean_Name_quickLt(v_declName_1507_, v_declName_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object* v_d_u2081_1510_, lean_object* v_d_u2082_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1510_, v_d_u2082_1511_);
lean_dec_ref(v_d_u2082_1511_);
lean_dec_ref(v_d_u2081_1510_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
v___x_1518_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState(void){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_s_1522_, lean_object* v_d_1523_){
_start:
{
lean_object* v_builtin_1524_; lean_object* v_newEntries_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1535_; 
v_builtin_1524_ = lean_ctor_get(v_s_1522_, 0);
v_newEntries_1525_ = lean_ctor_get(v_s_1522_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_s_1522_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1527_ = v_s_1522_;
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_newEntries_1525_);
lean_inc(v_builtin_1524_);
lean_dec(v_s_1522_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_declName_1529_; lean_object* v_keys_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v_declName_1529_ = lean_ctor_get(v_d_1523_, 0);
lean_inc(v_declName_1529_);
v_keys_1530_ = lean_ctor_get(v_d_1523_, 1);
lean_inc_ref(v_keys_1530_);
lean_dec_ref(v_d_1523_);
v___x_1531_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_1525_, v_declName_1529_, v_keys_1530_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1531_);
v___x_1533_ = v___x_1527_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_builtin_1524_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_result_1536_, lean_object* v_declName_1537_, lean_object* v_keys_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_declName_1537_);
lean_ctor_set(v___x_1539_, 1, v_keys_1538_);
v___x_1540_ = lean_array_push(v_result_1536_, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_1541_, lean_object* v_x1_1542_, lean_object* v_x2_1543_, lean_object* v_x3_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_apply_3(v_f_1541_, v_x1_1542_, v_x2_1543_, v_x3_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_1546_, lean_object* v_keys_1547_, lean_object* v_vals_1548_, lean_object* v_i_1549_, lean_object* v_acc_1550_){
_start:
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_array_get_size(v_keys_1547_);
v___x_1552_ = lean_nat_dec_lt(v_i_1549_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_dec(v_i_1549_);
lean_dec(v_f_1546_);
return v_acc_1550_;
}
else
{
lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_k_1553_ = lean_array_fget_borrowed(v_keys_1547_, v_i_1549_);
v_v_1554_ = lean_array_fget_borrowed(v_vals_1548_, v_i_1549_);
lean_inc(v_f_1546_);
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
v___x_1555_ = lean_apply_3(v_f_1546_, v_acc_1550_, v_k_1553_, v_v_1554_);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_i_1549_, v___x_1556_);
lean_dec(v_i_1549_);
v_i_1549_ = v___x_1557_;
v_acc_1550_ = v___x_1555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_1559_, lean_object* v_keys_1560_, lean_object* v_vals_1561_, lean_object* v_i_1562_, lean_object* v_acc_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1559_, v_keys_1560_, v_vals_1561_, v_i_1562_, v_acc_1563_);
lean_dec_ref(v_vals_1561_);
lean_dec_ref(v_keys_1560_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v_es_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_es_1568_ = lean_ctor_get(v_x_1566_, 0);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_array_get_size(v_es_1568_);
v___x_1571_ = lean_nat_dec_lt(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_dec(v_f_1565_);
return v_x_1567_;
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_le(v___x_1570_, v___x_1570_);
if (v___x_1572_ == 0)
{
if (v___x_1571_ == 0)
{
lean_dec(v_f_1565_);
return v_x_1567_;
}
else
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = lean_usize_of_nat(v___x_1570_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1565_, v_es_1568_, v___x_1573_, v___x_1574_, v_x_1567_);
return v___x_1575_;
}
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1570_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1565_, v_es_1568_, v___x_1576_, v___x_1577_, v_x_1567_);
return v___x_1578_;
}
}
}
else
{
lean_object* v_ks_1579_; lean_object* v_vs_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_ks_1579_ = lean_ctor_get(v_x_1566_, 0);
v_vs_1580_ = lean_ctor_get(v_x_1566_, 1);
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1565_, v_ks_1579_, v_vs_1580_, v___x_1581_, v_x_1567_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1583_, lean_object* v_as_1584_, size_t v_i_1585_, size_t v_stop_1586_, lean_object* v_b_1587_){
_start:
{
lean_object* v___y_1589_; uint8_t v___x_1593_; 
v___x_1593_ = lean_usize_dec_eq(v_i_1585_, v_stop_1586_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_array_uget_borrowed(v_as_1584_, v_i_1585_);
switch(lean_obj_tag(v___x_1594_))
{
case 0:
{
lean_object* v_key_1595_; lean_object* v_val_1596_; lean_object* v___x_1597_; 
v_key_1595_ = lean_ctor_get(v___x_1594_, 0);
v_val_1596_ = lean_ctor_get(v___x_1594_, 1);
lean_inc(v_f_1583_);
lean_inc(v_val_1596_);
lean_inc(v_key_1595_);
v___x_1597_ = lean_apply_3(v_f_1583_, v_b_1587_, v_key_1595_, v_val_1596_);
v___y_1589_ = v___x_1597_;
goto v___jp_1588_;
}
case 1:
{
lean_object* v_node_1598_; lean_object* v___x_1599_; 
v_node_1598_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_f_1583_);
v___x_1599_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1583_, v_node_1598_, v_b_1587_);
v___y_1589_ = v___x_1599_;
goto v___jp_1588_;
}
default: 
{
v___y_1589_ = v_b_1587_;
goto v___jp_1588_;
}
}
}
else
{
lean_dec(v_f_1583_);
return v_b_1587_;
}
v___jp_1588_:
{
size_t v___x_1590_; size_t v___x_1591_; 
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_i_1585_, v___x_1590_);
v_i_1585_ = v___x_1591_;
v_b_1587_ = v___y_1589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1600_, lean_object* v_as_1601_, lean_object* v_i_1602_, lean_object* v_stop_1603_, lean_object* v_b_1604_){
_start:
{
size_t v_i_boxed_1605_; size_t v_stop_boxed_1606_; lean_object* v_res_1607_; 
v_i_boxed_1605_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_stop_boxed_1606_ = lean_unbox_usize(v_stop_1603_);
lean_dec(v_stop_1603_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1600_, v_as_1601_, v_i_boxed_1605_, v_stop_boxed_1606_, v_b_1604_);
lean_dec_ref(v_as_1601_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1608_, v_x_1609_, v_x_1610_);
lean_dec_ref(v_x_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_1612_, lean_object* v_f_1613_, lean_object* v_init_1614_){
_start:
{
lean_object* v___f_1615_; lean_object* v___x_1616_; 
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1615_, 0, v_f_1613_);
v___x_1616_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1615_, v_map_1612_, v_init_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_1617_, lean_object* v_f_1618_, lean_object* v_init_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1617_, v_f_1618_, v_init_1619_);
lean_dec_ref(v_map_1617_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_1621_, lean_object* v_pivot_1622_, lean_object* v_as_1623_, lean_object* v_i_1624_, lean_object* v_k_1625_){
_start:
{
uint8_t v___x_1626_; 
v___x_1626_ = lean_nat_dec_lt(v_k_1625_, v_hi_1621_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_k_1625_);
v___x_1627_ = lean_array_fswap(v_as_1623_, v_i_1624_, v_hi_1621_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_i_1624_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
return v___x_1628_;
}
else
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = lean_array_fget_borrowed(v_as_1623_, v_k_1625_);
v___x_1630_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1629_, v_pivot_1622_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_add(v_k_1625_, v___x_1631_);
lean_dec(v_k_1625_);
v_k_1625_ = v___x_1632_;
goto _start;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_array_fswap(v_as_1623_, v_i_1624_, v_k_1625_);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_i_1624_, v___x_1635_);
lean_dec(v_i_1624_);
v___x_1637_ = lean_nat_add(v_k_1625_, v___x_1635_);
lean_dec(v_k_1625_);
v_as_1623_ = v___x_1634_;
v_i_1624_ = v___x_1636_;
v_k_1625_ = v___x_1637_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_1639_, lean_object* v_pivot_1640_, lean_object* v_as_1641_, lean_object* v_i_1642_, lean_object* v_k_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1639_, v_pivot_1640_, v_as_1641_, v_i_1642_, v_k_1643_);
lean_dec_ref(v_pivot_1640_);
lean_dec(v_hi_1639_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_1645_, lean_object* v_as_1646_, lean_object* v_lo_1647_, lean_object* v_hi_1648_){
_start:
{
lean_object* v___y_1650_; uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_lt(v_lo_1647_, v_hi_1648_);
if (v___x_1660_ == 0)
{
lean_dec(v_lo_1647_);
return v_as_1646_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v_mid_1663_; lean_object* v___y_1665_; lean_object* v___y_1671_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1661_ = lean_nat_add(v_lo_1647_, v_hi_1648_);
v___x_1662_ = lean_unsigned_to_nat(1u);
v_mid_1663_ = lean_nat_shiftr(v___x_1661_, v___x_1662_);
lean_dec(v___x_1661_);
v___x_1676_ = lean_array_fget_borrowed(v_as_1646_, v_mid_1663_);
v___x_1677_ = lean_array_fget_borrowed(v_as_1646_, v_lo_1647_);
v___x_1678_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
v___y_1671_ = v_as_1646_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_array_fswap(v_as_1646_, v_lo_1647_, v_mid_1663_);
v___y_1671_ = v___x_1679_;
goto v___jp_1670_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = lean_array_fget_borrowed(v___y_1665_, v_mid_1663_);
v___x_1667_ = lean_array_fget_borrowed(v___y_1665_, v_hi_1648_);
v___x_1668_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_dec(v_mid_1663_);
v___y_1650_ = v___y_1665_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_array_fswap(v___y_1665_, v_mid_1663_, v_hi_1648_);
lean_dec(v_mid_1663_);
v___y_1650_ = v___x_1669_;
goto v___jp_1649_;
}
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1672_ = lean_array_fget_borrowed(v___y_1671_, v_hi_1648_);
v___x_1673_ = lean_array_fget_borrowed(v___y_1671_, v_lo_1647_);
v___x_1674_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
v___y_1665_ = v___y_1671_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_array_fswap(v___y_1671_, v_lo_1647_, v_hi_1648_);
v___y_1665_ = v___x_1675_;
goto v___jp_1664_;
}
}
}
v___jp_1649_:
{
lean_object* v_pivot_1651_; lean_object* v___x_1652_; lean_object* v_fst_1653_; lean_object* v_snd_1654_; uint8_t v___x_1655_; 
v_pivot_1651_ = lean_array_fget(v___y_1650_, v_hi_1648_);
lean_inc_n(v_lo_1647_, 2);
v___x_1652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1648_, v_pivot_1651_, v___y_1650_, v_lo_1647_, v_lo_1647_);
lean_dec(v_pivot_1651_);
v_fst_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_fst_1653_);
v_snd_1654_ = lean_ctor_get(v___x_1652_, 1);
lean_inc(v_snd_1654_);
lean_dec_ref(v___x_1652_);
v___x_1655_ = lean_nat_dec_le(v_hi_1648_, v_fst_1653_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1645_, v_snd_1654_, v_lo_1647_, v_fst_1653_);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_add(v_fst_1653_, v___x_1657_);
lean_dec(v_fst_1653_);
v_as_1646_ = v___x_1656_;
v_lo_1647_ = v___x_1658_;
goto _start;
}
else
{
lean_dec(v_fst_1653_);
lean_dec(v_lo_1647_);
return v_snd_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_1680_, lean_object* v_as_1681_, lean_object* v_lo_1682_, lean_object* v_hi_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1680_, v_as_1681_, v_lo_1682_, v_hi_1683_);
lean_dec(v_hi_1683_);
lean_dec(v_n_1680_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1687_, lean_object* v_s_1688_){
_start:
{
lean_object* v_newEntries_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_result_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_newEntries_1689_ = lean_ctor_get(v_s_1688_, 1);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1692_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1689_, v___f_1687_, v___x_1691_);
v___x_1693_ = lean_array_get_size(v_result_1692_);
v___x_1694_ = lean_nat_dec_eq(v___x_1693_, v___x_1690_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___y_1698_; uint8_t v___x_1702_; 
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_sub(v___x_1693_, v___x_1695_);
v___x_1702_ = lean_nat_dec_le(v___x_1690_, v___x_1696_);
if (v___x_1702_ == 0)
{
lean_inc(v___x_1696_);
v___y_1698_ = v___x_1696_;
goto v___jp_1697_;
}
else
{
v___y_1698_ = v___x_1690_;
goto v___jp_1697_;
}
v___jp_1697_:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_nat_dec_le(v___y_1698_, v___x_1696_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec(v___x_1696_);
lean_inc(v___y_1698_);
v___x_1700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1693_, v_result_1692_, v___y_1698_, v___y_1698_);
lean_dec(v___y_1698_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1693_, v_result_1692_, v___y_1698_, v___x_1696_);
lean_dec(v___x_1696_);
return v___x_1701_;
}
}
}
else
{
return v_result_1692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1703_, lean_object* v_s_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1703_, v_s_1704_);
lean_dec_ref(v_s_1704_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_x_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_box(0);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_1708_);
lean_dec_ref(v_x_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1710_, lean_object* v_x_1711_, lean_object* v_s_1712_){
_start:
{
lean_object* v_newEntries_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v_result_1716_; lean_object* v___x_1717_; lean_object* v___y_1719_; lean_object* v___y_1720_; uint8_t v___x_1723_; 
v_newEntries_1713_ = lean_ctor_get(v_s_1712_, 1);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1716_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1713_, v___f_1710_, v___x_1715_);
v___x_1717_ = lean_array_get_size(v_result_1716_);
v___x_1723_ = lean_nat_dec_eq(v___x_1717_, v___x_1714_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___y_1727_; uint8_t v___x_1729_; 
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_sub(v___x_1717_, v___x_1724_);
v___x_1729_ = lean_nat_dec_le(v___x_1714_, v___x_1725_);
if (v___x_1729_ == 0)
{
lean_inc(v___x_1725_);
v___y_1727_ = v___x_1725_;
goto v___jp_1726_;
}
else
{
v___y_1727_ = v___x_1714_;
goto v___jp_1726_;
}
v___jp_1726_:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_nat_dec_le(v___y_1727_, v___x_1725_);
if (v___x_1728_ == 0)
{
lean_dec(v___x_1725_);
lean_inc(v___y_1727_);
v___y_1719_ = v___y_1727_;
v___y_1720_ = v___y_1727_;
goto v___jp_1718_;
}
else
{
v___y_1719_ = v___y_1727_;
v___y_1720_ = v___x_1725_;
goto v___jp_1718_;
}
}
}
else
{
lean_object* v___x_1730_; 
lean_inc_n(v_result_1716_, 2);
v___x_1730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1730_, 0, v_result_1716_);
lean_ctor_set(v___x_1730_, 1, v_result_1716_);
lean_ctor_set(v___x_1730_, 2, v_result_1716_);
return v___x_1730_;
}
v___jp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1717_, v_result_1716_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_inc_ref_n(v___x_1721_, 2);
v___x_1722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
lean_ctor_set(v___x_1722_, 2, v___x_1721_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1731_, lean_object* v_x_1732_, lean_object* v_s_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1731_, v_x_1732_, v_s_1733_);
lean_dec_ref(v_s_1733_);
lean_dec_ref(v_x_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v_keys_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1747_; 
v___x_1737_ = lean_st_ref_get(v___x_1735_);
v_keys_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v___x_1737_, 1);
lean_dec(v_unused_1748_);
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_keys_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_keys_1738_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1749_);
lean_dec(v___x_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1752_, lean_object* v_x_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v_keys_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1766_; 
v___x_1756_ = lean_st_ref_get(v___x_1752_);
v_keys_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1756_, 1);
lean_dec(v_unused_1767_);
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_keys_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1766_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_keys_1757_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1768_, v_x_1769_, v___y_1770_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v_x_1769_);
lean_dec(v___x_1768_);
return v_res_1772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___f_1788_; 
v___x_1787_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1788_, 0, v___x_1787_);
return v___f_1788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___f_1790_; 
v___x_1789_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_1790_, 0, v___x_1789_);
return v___f_1790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v___f_1794_; lean_object* v___f_1795_; lean_object* v___f_1796_; lean_object* v___f_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_box(2);
v___f_1793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___f_1797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1799_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___f_1797_);
lean_ctor_set(v___x_1799_, 2, v___f_1796_);
lean_ctor_set(v___x_1799_, 3, v___f_1795_);
lean_ctor_set(v___x_1799_, 4, v___f_1794_);
lean_ctor_set(v___x_1799_, 5, v___f_1793_);
lean_ctor_set(v___x_1799_, 6, v___x_1792_);
lean_ctor_set(v___x_1799_, 7, v___x_1791_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___f_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v___f_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1805_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_1808_, lean_object* v_00_u03b2_1809_, lean_object* v_map_1810_, lean_object* v_f_1811_, lean_object* v_init_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1810_, v_f_1811_, v_init_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_map_1816_, lean_object* v_f_1817_, lean_object* v_init_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_1814_, v_00_u03b2_1815_, v_map_1816_, v_f_1817_, v_init_1818_);
lean_dec_ref(v_map_1816_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object* v_n_1820_, lean_object* v_as_1821_, lean_object* v_lo_1822_, lean_object* v_hi_1823_, lean_object* v_w_1824_, lean_object* v_hlo_1825_, lean_object* v_hhi_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1820_, v_as_1821_, v_lo_1822_, v_hi_1823_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1828_, lean_object* v_as_1829_, lean_object* v_lo_1830_, lean_object* v_hi_1831_, lean_object* v_w_1832_, lean_object* v_hlo_1833_, lean_object* v_hhi_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_1828_, v_as_1829_, v_lo_1830_, v_hi_1831_, v_w_1832_, v_hlo_1833_, v_hhi_1834_);
lean_dec(v_hi_1831_);
lean_dec(v_n_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_1836_, lean_object* v_f_1837_, lean_object* v_init_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1837_, v_map_1836_, v_init_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_1840_, lean_object* v_f_1841_, lean_object* v_init_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1840_, v_f_1841_, v_init_1842_);
lean_dec_ref(v_map_1840_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_map_1846_, lean_object* v_f_1847_, lean_object* v_init_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1847_, v_map_1846_, v_init_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_map_1852_, lean_object* v_f_1853_, lean_object* v_init_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1850_, v_00_u03b2_1851_, v_map_1852_, v_f_1853_, v_init_1854_);
lean_dec_ref(v_map_1852_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_1856_, lean_object* v_lo_1857_, lean_object* v_hi_1858_, lean_object* v_hhi_1859_, lean_object* v_pivot_1860_, lean_object* v_as_1861_, lean_object* v_i_1862_, lean_object* v_k_1863_, lean_object* v_ilo_1864_, lean_object* v_ik_1865_, lean_object* v_w_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1858_, v_pivot_1860_, v_as_1861_, v_i_1862_, v_k_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_1868_, lean_object* v_lo_1869_, lean_object* v_hi_1870_, lean_object* v_hhi_1871_, lean_object* v_pivot_1872_, lean_object* v_as_1873_, lean_object* v_i_1874_, lean_object* v_k_1875_, lean_object* v_ilo_1876_, lean_object* v_ik_1877_, lean_object* v_w_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(v_n_1868_, v_lo_1869_, v_hi_1870_, v_hhi_1871_, v_pivot_1872_, v_as_1873_, v_i_1874_, v_k_1875_, v_ilo_1876_, v_ik_1877_, v_w_1878_);
lean_dec_ref(v_pivot_1872_);
lean_dec(v_hi_1870_);
lean_dec(v_lo_1869_);
lean_dec(v_n_1868_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1880_, lean_object* v_00_u03b1_1881_, lean_object* v_00_u03b2_1882_, lean_object* v_f_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1883_, v_x_1884_, v_x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1887_, lean_object* v_00_u03b1_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_f_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1887_, v_00_u03b1_1888_, v_00_u03b2_1889_, v_f_1890_, v_x_1891_, v_x_1892_);
lean_dec_ref(v_x_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_00_u03c3_1896_, lean_object* v_f_1897_, lean_object* v_as_1898_, size_t v_i_1899_, size_t v_stop_1900_, lean_object* v_b_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1897_, v_as_1898_, v_i_1899_, v_stop_1900_, v_b_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_00_u03c3_1905_, lean_object* v_f_1906_, lean_object* v_as_1907_, lean_object* v_i_1908_, lean_object* v_stop_1909_, lean_object* v_b_1910_){
_start:
{
size_t v_i_boxed_1911_; size_t v_stop_boxed_1912_; lean_object* v_res_1913_; 
v_i_boxed_1911_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_stop_boxed_1912_ = lean_unbox_usize(v_stop_1909_);
lean_dec(v_stop_1909_);
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1903_, v_00_u03b2_1904_, v_00_u03c3_1905_, v_f_1906_, v_as_1907_, v_i_boxed_1911_, v_stop_boxed_1912_, v_b_1910_);
lean_dec_ref(v_as_1907_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_1914_, lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_f_1917_, lean_object* v_keys_1918_, lean_object* v_vals_1919_, lean_object* v_heq_1920_, lean_object* v_i_1921_, lean_object* v_acc_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1917_, v_keys_1918_, v_vals_1919_, v_i_1921_, v_acc_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_1924_, lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_f_1927_, lean_object* v_keys_1928_, lean_object* v_vals_1929_, lean_object* v_heq_1930_, lean_object* v_i_1931_, lean_object* v_acc_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_1924_, v_00_u03b1_1925_, v_00_u03b2_1926_, v_f_1927_, v_keys_1928_, v_vals_1929_, v_heq_1930_, v_i_1931_, v_acc_1932_);
lean_dec_ref(v_vals_1929_);
lean_dec_ref(v_keys_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object* v_a_1934_, lean_object* v_x_1935_){
_start:
{
if (lean_obj_tag(v_x_1935_) == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_box(0);
return v___x_1936_;
}
else
{
lean_object* v_key_1937_; lean_object* v_value_1938_; lean_object* v_tail_1939_; uint8_t v___x_1940_; 
v_key_1937_ = lean_ctor_get(v_x_1935_, 0);
v_value_1938_ = lean_ctor_get(v_x_1935_, 1);
v_tail_1939_ = lean_ctor_get(v_x_1935_, 2);
v___x_1940_ = lean_name_eq(v_key_1937_, v_a_1934_);
if (v___x_1940_ == 0)
{
v_x_1935_ = v_tail_1939_;
goto _start;
}
else
{
lean_object* v___x_1942_; 
lean_inc(v_value_1938_);
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_value_1938_);
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1943_, v_x_1944_);
lean_dec(v_x_1944_);
lean_dec(v_a_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_buckets_1948_; lean_object* v___x_1949_; uint64_t v___y_1951_; 
v_buckets_1948_ = lean_ctor_get(v_m_1946_, 1);
v___x_1949_ = lean_array_get_size(v_buckets_1948_);
if (lean_obj_tag(v_a_1947_) == 0)
{
uint64_t v___x_1965_; 
v___x_1965_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1951_ = v___x_1965_;
goto v___jp_1950_;
}
else
{
uint64_t v_hash_1966_; 
v_hash_1966_ = lean_ctor_get_uint64(v_a_1947_, sizeof(void*)*2);
v___y_1951_ = v_hash_1966_;
goto v___jp_1950_;
}
v___jp_1950_:
{
uint64_t v___x_1952_; uint64_t v___x_1953_; uint64_t v_fold_1954_; uint64_t v___x_1955_; uint64_t v___x_1956_; uint64_t v___x_1957_; size_t v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1952_ = 32ULL;
v___x_1953_ = lean_uint64_shift_right(v___y_1951_, v___x_1952_);
v_fold_1954_ = lean_uint64_xor(v___y_1951_, v___x_1953_);
v___x_1955_ = 16ULL;
v___x_1956_ = lean_uint64_shift_right(v_fold_1954_, v___x_1955_);
v___x_1957_ = lean_uint64_xor(v_fold_1954_, v___x_1956_);
v___x_1958_ = lean_uint64_to_usize(v___x_1957_);
v___x_1959_ = lean_usize_of_nat(v___x_1949_);
v___x_1960_ = ((size_t)1ULL);
v___x_1961_ = lean_usize_sub(v___x_1959_, v___x_1960_);
v___x_1962_ = lean_usize_land(v___x_1958_, v___x_1961_);
v___x_1963_ = lean_array_uget_borrowed(v_buckets_1948_, v___x_1962_);
v___x_1964_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1947_, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_m_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_1970_, lean_object* v_k_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_m_1976_; lean_object* v_a_1977_; uint8_t v___x_1978_; 
v___x_1974_ = lean_nat_add(v_x_1972_, v_x_1973_);
v___x_1975_ = lean_unsigned_to_nat(1u);
v_m_1976_ = lean_nat_shiftr(v___x_1974_, v___x_1975_);
lean_dec(v___x_1974_);
v_a_1977_ = lean_array_fget_borrowed(v_as_1970_, v_m_1976_);
v___x_1978_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_1977_, v_k_1971_);
if (v___x_1978_ == 0)
{
uint8_t v___x_1979_; 
lean_dec(v_x_1973_);
v___x_1979_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_1971_, v_a_1977_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec(v_m_1976_);
lean_dec(v_x_1972_);
lean_inc(v_a_1977_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1977_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_nat_dec_eq(v_m_1976_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = lean_nat_sub(v_m_1976_, v___x_1975_);
lean_dec(v_m_1976_);
v___x_1984_ = lean_nat_dec_lt(v___x_1983_, v_x_1972_);
if (v___x_1984_ == 0)
{
v_x_1973_ = v___x_1983_;
goto _start;
}
else
{
lean_object* v___x_1986_; 
lean_dec(v___x_1983_);
lean_dec(v_x_1972_);
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
}
else
{
lean_object* v___x_1987_; 
lean_dec(v_m_1976_);
lean_dec(v_x_1972_);
v___x_1987_ = lean_box(0);
return v___x_1987_;
}
}
}
else
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
lean_dec(v_x_1972_);
v___x_1988_ = lean_nat_add(v_m_1976_, v___x_1975_);
lean_dec(v_m_1976_);
v___x_1989_ = lean_nat_dec_le(v___x_1988_, v_x_1973_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec(v___x_1988_);
lean_dec(v_x_1973_);
v___x_1990_ = lean_box(0);
return v___x_1990_;
}
else
{
v_x_1972_ = v___x_1988_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_1992_, lean_object* v_k_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_1992_, v_k_1993_, v_x_1994_, v_x_1995_);
lean_dec_ref(v_k_1993_);
lean_dec_ref(v_as_1992_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_1997_, lean_object* v_vals_1998_, lean_object* v_i_1999_, lean_object* v_k_2000_){
_start:
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = lean_array_get_size(v_keys_1997_);
v___x_2002_ = lean_nat_dec_lt(v_i_1999_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec(v_i_1999_);
v___x_2003_ = lean_box(0);
return v___x_2003_;
}
else
{
lean_object* v_k_x27_2004_; uint8_t v___x_2005_; 
v_k_x27_2004_ = lean_array_fget_borrowed(v_keys_1997_, v_i_1999_);
v___x_2005_ = lean_name_eq(v_k_2000_, v_k_x27_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_add(v_i_1999_, v___x_2006_);
lean_dec(v_i_1999_);
v_i_1999_ = v___x_2007_;
goto _start;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_array_fget_borrowed(v_vals_1998_, v_i_1999_);
lean_dec(v_i_1999_);
lean_inc(v___x_2009_);
v___x_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2011_, lean_object* v_vals_2012_, lean_object* v_i_2013_, lean_object* v_k_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2011_, v_vals_2012_, v_i_2013_, v_k_2014_);
lean_dec(v_k_2014_);
lean_dec_ref(v_vals_2012_);
lean_dec_ref(v_keys_2011_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object* v_x_2016_, size_t v_x_2017_, lean_object* v_x_2018_){
_start:
{
if (lean_obj_tag(v_x_2016_) == 0)
{
lean_object* v_es_2019_; lean_object* v___x_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v_j_2023_; lean_object* v___x_2024_; 
v_es_2019_ = lean_ctor_get(v_x_2016_, 0);
v___x_2020_ = lean_box(2);
v___x_2021_ = ((size_t)31ULL);
v___x_2022_ = lean_usize_land(v_x_2017_, v___x_2021_);
v_j_2023_ = lean_usize_to_nat(v___x_2022_);
v___x_2024_ = lean_array_get_borrowed(v___x_2020_, v_es_2019_, v_j_2023_);
lean_dec(v_j_2023_);
switch(lean_obj_tag(v___x_2024_))
{
case 0:
{
lean_object* v_key_2025_; lean_object* v_val_2026_; uint8_t v___x_2027_; 
v_key_2025_ = lean_ctor_get(v___x_2024_, 0);
v_val_2026_ = lean_ctor_get(v___x_2024_, 1);
v___x_2027_ = lean_name_eq(v_x_2018_, v_key_2025_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_box(0);
return v___x_2028_;
}
else
{
lean_object* v___x_2029_; 
lean_inc(v_val_2026_);
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_val_2026_);
return v___x_2029_;
}
}
case 1:
{
lean_object* v_node_2030_; size_t v___x_2031_; size_t v___x_2032_; 
v_node_2030_ = lean_ctor_get(v___x_2024_, 0);
v___x_2031_ = ((size_t)5ULL);
v___x_2032_ = lean_usize_shift_right(v_x_2017_, v___x_2031_);
v_x_2016_ = v_node_2030_;
v_x_2017_ = v___x_2032_;
goto _start;
}
default: 
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_box(0);
return v___x_2034_;
}
}
}
else
{
lean_object* v_ks_2035_; lean_object* v_vs_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v_ks_2035_ = lean_ctor_get(v_x_2016_, 0);
v_vs_2036_ = lean_ctor_get(v_x_2016_, 1);
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_2035_, v_vs_2036_, v___x_2037_, v_x_2018_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
size_t v_x_1432__boxed_2042_; lean_object* v_res_2043_; 
v_x_1432__boxed_2042_ = lean_unbox_usize(v_x_2040_);
lean_dec(v_x_2040_);
v_res_2043_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2039_, v_x_1432__boxed_2042_, v_x_2041_);
lean_dec(v_x_2041_);
lean_dec_ref(v_x_2039_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
uint64_t v___y_2047_; 
if (lean_obj_tag(v_x_2045_) == 0)
{
uint64_t v___x_2050_; 
v___x_2050_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2047_ = v___x_2050_;
goto v___jp_2046_;
}
else
{
uint64_t v_hash_2051_; 
v_hash_2051_ = lean_ctor_get_uint64(v_x_2045_, sizeof(void*)*2);
v___y_2047_ = v_hash_2051_;
goto v___jp_2046_;
}
v___jp_2046_:
{
size_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_uint64_to_usize(v___y_2047_);
v___x_2049_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2044_, v___x_2048_, v_x_2045_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2052_, v_x_2053_);
lean_dec(v_x_2053_);
lean_dec_ref(v_x_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object* v_declName_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v_env_2059_; lean_object* v___x_2060_; lean_object* v___x_2070_; 
v___x_2058_ = lean_st_ref_get(v_a_2056_);
v_env_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc_ref(v_env_2059_);
lean_dec(v___x_2058_);
v___x_2060_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2070_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2059_, v_declName_2055_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; lean_object* v_toEnvExtension_2072_; lean_object* v_asyncMode_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_newEntries_2076_; lean_object* v___x_2077_; 
v___x_2071_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2072_ = lean_ctor_get(v___x_2071_, 0);
v_asyncMode_2073_ = lean_ctor_get(v_toEnvExtension_2072_, 2);
v___x_2074_ = lean_box(0);
lean_inc_ref(v_env_2059_);
v___x_2075_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2060_, v___x_2071_, v_env_2059_, v_asyncMode_2073_, v___x_2074_);
v_newEntries_2076_ = lean_ctor_get(v___x_2075_, 1);
lean_inc_ref(v_newEntries_2076_);
lean_dec(v___x_2075_);
v___x_2077_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_2076_, v_declName_2055_);
lean_dec_ref(v_newEntries_2076_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v___x_2078_; 
lean_dec_ref(v_env_2059_);
lean_dec(v_declName_2055_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
else
{
lean_dec(v___x_2077_);
goto v___jp_2061_;
}
}
else
{
lean_object* v_val_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2107_; 
v_val_2079_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2081_ = v___x_2070_;
v_isShared_2082_ = v_isSharedCheck_2107_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_val_2079_);
lean_dec(v___x_2070_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2107_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2083_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v___x_2084_ = 0;
v___x_2085_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2060_, v___x_2083_, v_env_2059_, v_val_2079_, v___x_2084_);
lean_dec(v_val_2079_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_array_get_size(v___x_2085_);
v___x_2088_ = lean_nat_dec_lt(v___x_2086_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v___x_2085_);
lean_del_object(v___x_2081_);
goto v___jp_2061_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2090_ = lean_nat_sub(v___x_2087_, v___x_2089_);
v___x_2091_ = lean_nat_dec_le(v___x_2086_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_dec(v___x_2090_);
lean_dec_ref(v___x_2085_);
lean_del_object(v___x_2081_);
goto v___jp_2061_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0));
lean_inc(v_declName_2055_);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_declName_2055_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_2085_, v___x_2093_, v___x_2086_, v___x_2090_);
lean_dec_ref_known(v___x_2093_, 2);
lean_dec_ref(v___x_2085_);
if (lean_obj_tag(v___x_2094_) == 1)
{
lean_object* v_val_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_env_2059_);
lean_dec(v_declName_2055_);
v_val_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_val_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_keys_2099_; lean_object* v___x_2101_; 
v_keys_2099_ = lean_ctor_get(v_val_2095_, 1);
lean_inc_ref(v_keys_2099_);
lean_dec(v_val_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v_keys_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_keys_2099_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2101_);
v___x_2103_ = v___x_2081_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_dec(v___x_2094_);
lean_del_object(v___x_2081_);
goto v___jp_2061_;
}
}
}
}
}
v___jp_2061_:
{
lean_object* v___x_2062_; lean_object* v_toEnvExtension_2063_; lean_object* v_asyncMode_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_builtin_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2062_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2063_ = lean_ctor_get(v___x_2062_, 0);
v_asyncMode_2064_ = lean_ctor_get(v_toEnvExtension_2063_, 2);
v___x_2065_ = lean_box(0);
v___x_2066_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2060_, v___x_2062_, v_env_2059_, v_asyncMode_2064_, v___x_2065_);
v_builtin_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_builtin_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_2067_, v_declName_2055_);
lean_dec(v_declName_2055_);
lean_dec_ref(v_builtin_2067_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2108_, v_a_2109_);
lean_dec(v_a_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object* v_declName_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2112_, v_a_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object* v_declName_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_2122_, lean_object* v_m_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2123_, v_a_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_2126_, lean_object* v_m_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_2126_, v_m_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_m_2127_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_2134_, v_x_2135_, v_x_2136_);
lean_dec(v_x_2136_);
lean_dec_ref(v_x_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object* v_as_2138_, lean_object* v_k_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2138_, v_k_2139_, v_x_2140_, v_x_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_2144_, lean_object* v_k_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(v_as_2144_, v_k_2145_, v_x_2146_, v_x_2147_, v_x_2148_);
lean_dec_ref(v_k_2145_);
lean_dec_ref(v_as_2144_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2150_, lean_object* v_a_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2154_, lean_object* v_a_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_2154_, v_a_2155_, v_x_2156_);
lean_dec(v_x_2156_);
lean_dec(v_a_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2158_, lean_object* v_x_2159_, size_t v_x_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2159_, v_x_2160_, v_x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
size_t v_x_1619__boxed_2167_; lean_object* v_res_2168_; 
v_x_1619__boxed_2167_ = lean_unbox_usize(v_x_2165_);
lean_dec(v_x_2165_);
v_res_2168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_2163_, v_x_2164_, v_x_1619__boxed_2167_, v_x_2166_);
lean_dec(v_x_2166_);
lean_dec_ref(v_x_2164_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2169_, lean_object* v_keys_2170_, lean_object* v_vals_2171_, lean_object* v_heq_2172_, lean_object* v_i_2173_, lean_object* v_k_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2170_, v_vals_2171_, v_i_2173_, v_k_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_keys_2177_, lean_object* v_vals_2178_, lean_object* v_heq_2179_, lean_object* v_i_2180_, lean_object* v_k_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_2176_, v_keys_2177_, v_vals_2178_, v_heq_2179_, v_i_2180_, v_k_2181_);
lean_dec(v_k_2181_);
lean_dec_ref(v_vals_2178_);
lean_dec_ref(v_keys_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object* v_declName_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v___x_2186_; lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2201_; 
v___x_2186_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2183_, v_a_2184_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2201_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2201_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
if (lean_obj_tag(v_a_2187_) == 0)
{
uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = 0;
v___x_2192_ = lean_box(v___x_2191_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
else
{
uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_dec_ref_known(v_a_2187_, 1);
v___x_2196_ = 1;
v___x_2197_ = lean_box(v___x_2196_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2197_);
v___x_2199_ = v___x_2189_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object* v_declName_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2202_, v_a_2203_);
lean_dec(v_a_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object* v_declName_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2206_, v_a_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object* v_declName_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object* v_declName_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___x_2219_; lean_object* v_env_2220_; lean_object* v___x_2221_; lean_object* v_toEnvExtension_2222_; lean_object* v_asyncMode_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_builtin_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2219_ = lean_st_ref_get(v_a_2217_);
v_env_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc_ref(v_env_2220_);
lean_dec(v___x_2219_);
v___x_2221_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2222_ = lean_ctor_get(v___x_2221_, 0);
v_asyncMode_2223_ = lean_ctor_get(v_toEnvExtension_2222_, 2);
v___x_2224_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2225_ = lean_box(0);
v___x_2226_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2224_, v___x_2221_, v_env_2220_, v_asyncMode_2223_, v___x_2225_);
v_builtin_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc_ref(v_builtin_2227_);
lean_dec(v___x_2226_);
v___x_2228_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_2227_, v_declName_2216_);
lean_dec_ref(v_builtin_2227_);
v___x_2229_ = lean_box(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object* v_declName_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec(v_declName_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object* v_declName_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2235_, v_a_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object* v_declName_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_declName_2240_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object* v_declName_2245_, lean_object* v_keys_2246_, lean_object* v_s_2247_){
_start:
{
lean_object* v_builtin_2248_; lean_object* v_newEntries_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2257_; 
v_builtin_2248_ = lean_ctor_get(v_s_2247_, 0);
v_newEntries_2249_ = lean_ctor_get(v_s_2247_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_s_2247_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2251_ = v_s_2247_;
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_newEntries_2249_);
lean_inc(v_builtin_2248_);
lean_dec(v_s_2247_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_2249_, v_declName_2245_, v_keys_2246_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 1, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_builtin_2248_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
lean_ctor_set(v___x_2263_, 2, v___x_2262_);
lean_ctor_set(v___x_2263_, 3, v___x_2262_);
lean_ctor_set(v___x_2263_, 4, v___x_2261_);
lean_ctor_set(v___x_2263_, 5, v___x_2261_);
lean_ctor_set(v___x_2263_, 6, v___x_2261_);
lean_ctor_set(v___x_2263_, 7, v___x_2261_);
lean_ctor_set(v___x_2263_, 8, v___x_2261_);
lean_ctor_set(v___x_2263_, 9, v___x_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_unsigned_to_nat(32u);
v___x_2265_ = lean_mk_empty_array_with_capacity(v___x_2264_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2267_ = ((size_t)5ULL);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_unsigned_to_nat(32u);
v___x_2270_ = lean_mk_empty_array_with_capacity(v___x_2269_);
v___x_2271_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
v___x_2272_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2270_);
lean_ctor_set(v___x_2272_, 2, v___x_2268_);
lean_ctor_set(v___x_2272_, 3, v___x_2268_);
lean_ctor_set_usize(v___x_2272_, 4, v___x_2267_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = lean_box(1);
v___x_2274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
v___x_2275_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_2274_);
lean_ctor_set(v___x_2276_, 2, v___x_2273_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object* v_msgData_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v_env_2282_; lean_object* v_options_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2281_ = lean_st_ref_get(v___y_2279_);
v_env_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc_ref(v_env_2282_);
lean_dec(v___x_2281_);
v_options_2283_ = lean_ctor_get(v___y_2278_, 2);
v___x_2284_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2285_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2283_);
v___x_2286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2286_, 0, v_env_2282_);
lean_ctor_set(v___x_2286_, 1, v___x_2284_);
lean_ctor_set(v___x_2286_, 2, v___x_2285_);
lean_ctor_set(v___x_2286_, 3, v_options_2283_);
v___x_2287_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_msgData_2277_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_ref_2298_; lean_object* v___x_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_ref_2298_ = lean_ctor_get(v___y_2295_, 5);
v___x_2299_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_2294_, v___y_2295_, v___y_2296_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_inc(v_ref_2298_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_ref_2298_);
lean_ctor_set(v___x_2304_, 1, v_a_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set_tag(v___x_2302_, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2313_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0(void){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3));
v___x_2321_ = l_Lean_stringToMessageData(v___x_2320_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6));
v___x_2326_ = l_Lean_stringToMessageData(v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object* v_declName_2327_, lean_object* v_keys_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v_env_2333_; lean_object* v___f_2334_; lean_object* v___y_2336_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___x_2384_; 
v___x_2332_ = lean_st_ref_get(v_a_2330_);
v_env_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_ref(v_env_2333_);
lean_dec(v___x_2332_);
lean_inc(v_declName_2327_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0), 3, 2);
lean_closure_set(v___f_2334_, 0, v_declName_2327_);
lean_closure_set(v___f_2334_, 1, v_keys_2328_);
v___x_2384_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2333_, v_declName_2327_);
lean_dec_ref(v_env_2333_);
if (lean_obj_tag(v___x_2384_) == 0)
{
v___y_2364_ = v_a_2329_;
v___y_2365_ = v_a_2330_;
goto v___jp_2363_;
}
else
{
uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec_ref_known(v___x_2384_, 1);
lean_dec_ref(v___f_2334_);
v___x_2385_ = 0;
v___x_2386_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2387_ = l_Lean_MessageData_ofConstName(v_declName_2327_, v___x_2385_);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2390_, v_a_2329_, v_a_2330_);
return v___x_2391_;
}
v___jp_2335_:
{
lean_object* v___x_2337_; lean_object* v_env_2338_; lean_object* v_nextMacroScope_2339_; lean_object* v_ngen_2340_; lean_object* v_auxDeclNGen_2341_; lean_object* v_traceState_2342_; lean_object* v_messages_2343_; lean_object* v_infoState_2344_; lean_object* v_snapshotTasks_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2361_; 
v___x_2337_ = lean_st_ref_take(v___y_2336_);
v_env_2338_ = lean_ctor_get(v___x_2337_, 0);
v_nextMacroScope_2339_ = lean_ctor_get(v___x_2337_, 1);
v_ngen_2340_ = lean_ctor_get(v___x_2337_, 2);
v_auxDeclNGen_2341_ = lean_ctor_get(v___x_2337_, 3);
v_traceState_2342_ = lean_ctor_get(v___x_2337_, 4);
v_messages_2343_ = lean_ctor_get(v___x_2337_, 6);
v_infoState_2344_ = lean_ctor_get(v___x_2337_, 7);
v_snapshotTasks_2345_ = lean_ctor_get(v___x_2337_, 8);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v___x_2337_, 5);
lean_dec(v_unused_2362_);
v___x_2347_ = v___x_2337_;
v_isShared_2348_ = v_isSharedCheck_2361_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_snapshotTasks_2345_);
lean_inc(v_infoState_2344_);
lean_inc(v_messages_2343_);
lean_inc(v_traceState_2342_);
lean_inc(v_auxDeclNGen_2341_);
lean_inc(v_ngen_2340_);
lean_inc(v_nextMacroScope_2339_);
lean_inc(v_env_2338_);
lean_dec(v___x_2337_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2361_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v_toEnvExtension_2350_; lean_object* v_asyncMode_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2349_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2350_ = lean_ctor_get(v___x_2349_, 0);
v_asyncMode_2351_ = lean_ctor_get(v_toEnvExtension_2350_, 2);
v___x_2352_ = lean_box(0);
v___x_2353_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2349_, v_env_2338_, v___f_2334_, v_asyncMode_2351_, v___x_2352_);
v___x_2354_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 5, v___x_2354_);
lean_ctor_set(v___x_2347_, 0, v___x_2353_);
v___x_2356_ = v___x_2347_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_nextMacroScope_2339_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_ngen_2340_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_auxDeclNGen_2341_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_traceState_2342_);
lean_ctor_set(v_reuseFailAlloc_2360_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2360_, 6, v_messages_2343_);
lean_ctor_set(v_reuseFailAlloc_2360_, 7, v_infoState_2344_);
lean_ctor_set(v_reuseFailAlloc_2360_, 8, v_snapshotTasks_2345_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_st_ref_set(v___y_2336_, v___x_2356_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
}
v___jp_2363_:
{
lean_object* v___x_2366_; 
lean_inc(v_declName_2327_);
v___x_2366_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2327_, v___y_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; uint8_t v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_unbox(v_a_2367_);
lean_dec(v_a_2367_);
if (v___x_2368_ == 0)
{
lean_dec(v_declName_2327_);
v___y_2336_ = v___y_2365_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v___f_2334_);
v___x_2369_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2370_ = 0;
v___x_2371_ = l_Lean_MessageData_ofConstName(v_declName_2327_, v___x_2370_);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2369_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2374_, v___y_2364_, v___y_2365_);
return v___x_2375_;
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v___f_2334_);
lean_dec(v_declName_2327_);
v_a_2376_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2366_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2366_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object* v_declName_2392_, lean_object* v_keys_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2392_, v_keys_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object* v_00_u03b1_2398_, lean_object* v_msg_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2399_, v___y_2400_, v___y_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_msg_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(v_00_u03b1_2404_, v_msg_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_2410_){
_start:
{
if (lean_obj_tag(v_e_2410_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2420_; 
v_a_2412_ = lean_ctor_get(v_e_2410_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_e_2410_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2414_ = v_e_2410_;
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v_e_2410_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = lean_mk_io_user_error(v_a_2412_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 1);
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
v_a_2421_ = lean_ctor_get(v_e_2410_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_e_2410_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v_e_2410_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v_e_2410_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 0);
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2429_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_2432_, lean_object* v_e_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2433_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_2436_, lean_object* v_e_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(v_00_u03b1_2436_, v_e_2437_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object* v_declName_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_env_2450_; lean_object* v_opts_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; 
v_env_2450_ = lean_ctor_get(v_a_2448_, 0);
v_opts_2451_ = lean_ctor_get(v_a_2448_, 1);
v___x_2452_ = 0;
lean_inc(v_declName_2447_);
lean_inc_ref(v_env_2450_);
v___x_2453_ = l_Lean_Environment_find_x3f(v_env_2450_, v_declName_2447_, v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2454_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0));
v___x_2455_ = 1;
v___x_2456_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2447_, v___x_2455_);
v___x_2457_ = lean_string_append(v___x_2454_, v___x_2456_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2459_ = lean_string_append(v___x_2457_, v___x_2458_);
v___x_2460_ = lean_mk_io_user_error(v___x_2459_);
v___x_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2507_; 
v_val_2462_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2464_ = v___x_2453_;
v_isShared_2465_ = v_isSharedCheck_2507_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_val_2462_);
lean_dec(v___x_2453_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2507_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_ConstantInfo_type(v_val_2462_);
if (lean_obj_tag(v___x_2483_) == 4)
{
lean_object* v_declName_2484_; 
v_declName_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_declName_2484_);
lean_dec_ref_known(v___x_2483_, 2);
if (lean_obj_tag(v_declName_2484_) == 1)
{
lean_object* v_pre_2485_; 
v_pre_2485_ = lean_ctor_get(v_declName_2484_, 0);
lean_inc(v_pre_2485_);
if (lean_obj_tag(v_pre_2485_) == 1)
{
lean_object* v_pre_2486_; 
v_pre_2486_ = lean_ctor_get(v_pre_2485_, 0);
lean_inc(v_pre_2486_);
if (lean_obj_tag(v_pre_2486_) == 1)
{
lean_object* v_pre_2487_; 
v_pre_2487_ = lean_ctor_get(v_pre_2486_, 0);
lean_inc(v_pre_2487_);
if (lean_obj_tag(v_pre_2487_) == 1)
{
lean_object* v_pre_2488_; 
v_pre_2488_ = lean_ctor_get(v_pre_2487_, 0);
lean_inc(v_pre_2488_);
if (lean_obj_tag(v_pre_2488_) == 1)
{
lean_object* v_pre_2489_; 
v_pre_2489_ = lean_ctor_get(v_pre_2488_, 0);
if (lean_obj_tag(v_pre_2489_) == 0)
{
lean_object* v_str_2490_; lean_object* v_str_2491_; lean_object* v_str_2492_; lean_object* v_str_2493_; lean_object* v_str_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_str_2490_ = lean_ctor_get(v_declName_2484_, 1);
lean_inc_ref(v_str_2490_);
lean_dec_ref_known(v_declName_2484_, 2);
v_str_2491_ = lean_ctor_get(v_pre_2485_, 1);
lean_inc_ref(v_str_2491_);
lean_dec_ref_known(v_pre_2485_, 2);
v_str_2492_ = lean_ctor_get(v_pre_2486_, 1);
lean_inc_ref(v_str_2492_);
lean_dec_ref_known(v_pre_2486_, 2);
v_str_2493_ = lean_ctor_get(v_pre_2487_, 1);
lean_inc_ref(v_str_2493_);
lean_dec_ref_known(v_pre_2487_, 2);
v_str_2494_ = lean_ctor_get(v_pre_2488_, 1);
lean_inc_ref(v_str_2494_);
lean_dec_ref_known(v_pre_2488_, 2);
v___x_2495_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0));
v___x_2496_ = lean_string_dec_eq(v_str_2494_, v___x_2495_);
lean_dec_ref(v_str_2494_);
if (v___x_2496_ == 0)
{
lean_dec_ref(v_str_2493_);
lean_dec_ref(v_str_2492_);
lean_dec_ref(v_str_2491_);
lean_dec_ref(v_str_2490_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2497_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1));
v___x_2498_ = lean_string_dec_eq(v_str_2493_, v___x_2497_);
lean_dec_ref(v_str_2493_);
if (v___x_2498_ == 0)
{
lean_dec_ref(v_str_2492_);
lean_dec_ref(v_str_2491_);
lean_dec_ref(v_str_2490_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4));
v___x_2500_ = lean_string_dec_eq(v_str_2492_, v___x_2499_);
lean_dec_ref(v_str_2492_);
if (v___x_2500_ == 0)
{
lean_dec_ref(v_str_2491_);
lean_dec_ref(v_str_2490_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5));
v___x_2502_ = lean_string_dec_eq(v_str_2491_, v___x_2501_);
lean_dec_ref(v_str_2491_);
if (v___x_2502_ == 0)
{
lean_dec_ref(v_str_2490_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6));
v___x_2504_ = lean_string_dec_eq(v_str_2490_, v___x_2503_);
lean_dec_ref(v_str_2490_);
if (v___x_2504_ == 0)
{
goto v___jp_2466_;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_del_object(v___x_2464_);
lean_dec(v_val_2462_);
v___x_2505_ = l_Lean_Environment_evalConst___redArg(v_env_2450_, v_opts_2451_, v_declName_2447_, v___x_2504_);
lean_dec(v_declName_2447_);
v___x_2506_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_2505_);
return v___x_2506_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2488_, 2);
lean_dec_ref_known(v_pre_2487_, 2);
lean_dec_ref_known(v_pre_2486_, 2);
lean_dec_ref_known(v_pre_2485_, 2);
lean_dec_ref_known(v_declName_2484_, 2);
goto v___jp_2466_;
}
}
else
{
lean_dec_ref_known(v_pre_2487_, 2);
lean_dec(v_pre_2488_);
lean_dec_ref_known(v_pre_2486_, 2);
lean_dec_ref_known(v_pre_2485_, 2);
lean_dec_ref_known(v_declName_2484_, 2);
goto v___jp_2466_;
}
}
else
{
lean_dec(v_pre_2487_);
lean_dec_ref_known(v_pre_2486_, 2);
lean_dec_ref_known(v_pre_2485_, 2);
lean_dec_ref_known(v_declName_2484_, 2);
goto v___jp_2466_;
}
}
else
{
lean_dec_ref_known(v_pre_2485_, 2);
lean_dec(v_pre_2486_);
lean_dec_ref_known(v_declName_2484_, 2);
goto v___jp_2466_;
}
}
else
{
lean_dec_ref_known(v_declName_2484_, 2);
lean_dec(v_pre_2485_);
goto v___jp_2466_;
}
}
else
{
lean_dec(v_declName_2484_);
goto v___jp_2466_;
}
}
else
{
lean_dec_ref(v___x_2483_);
goto v___jp_2466_;
}
v___jp_2466_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2467_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2));
v___x_2468_ = l_Lean_privateToUserName(v_declName_2447_);
v___x_2469_ = 1;
v___x_2470_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2468_, v___x_2469_);
v___x_2471_ = lean_string_append(v___x_2467_, v___x_2470_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3));
v___x_2473_ = lean_string_append(v___x_2471_, v___x_2472_);
v___x_2474_ = l_Lean_ConstantInfo_type(v_val_2462_);
lean_dec(v_val_2462_);
v___x_2475_ = lean_expr_dbg_to_string(v___x_2474_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_string_append(v___x_2473_, v___x_2475_);
lean_dec_ref(v___x_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2478_ = lean_string_append(v___x_2476_, v___x_2477_);
v___x_2479_ = lean_mk_io_user_error(v___x_2478_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2479_);
v___x_2481_ = v___x_2464_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object* v_declName_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2508_, v_a_2509_);
lean_dec_ref(v_a_2509_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object* v_e_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_declName_2515_; lean_object* v___x_2516_; 
v_declName_2515_ = lean_ctor_get(v_e_2512_, 0);
lean_inc(v_declName_2515_);
v___x_2516_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2515_, v_a_2513_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2525_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2525_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_e_2512_);
lean_ctor_set(v___x_2521_, 1, v_a_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_e_2512_);
v_a_2526_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2516_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2516_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object* v_e_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2534_, v_a_2535_);
lean_dec_ref(v_a_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
v___x_2540_ = lean_st_mk_ref(v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___y_2544_){
_start:
{
lean_inc_ref(v___y_2544_);
return v___y_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_2545_);
lean_dec_ref(v___y_2545_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_2548_, v___y_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2552_, v___y_2553_, v___y_2554_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v_x_2552_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_e_2557_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2558_; 
v_toCbvSimprocOLeanEntry_2558_ = lean_ctor_get(v_e_2557_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2558_);
return v_toCbvSimprocOLeanEntry_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_e_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_2559_);
lean_dec_ref(v_e_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_s_2561_, lean_object* v_e_2562_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2563_; lean_object* v_proc_2564_; lean_object* v_declName_2565_; uint8_t v_phase_2566_; lean_object* v_keys_2567_; lean_object* v___x_2568_; 
v_toCbvSimprocOLeanEntry_2563_ = lean_ctor_get(v_e_2562_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2563_);
v_proc_2564_ = lean_ctor_get(v_e_2562_, 1);
lean_inc_ref(v_proc_2564_);
lean_dec_ref(v_e_2562_);
v_declName_2565_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2563_, 0);
lean_inc(v_declName_2565_);
v_phase_2566_ = lean_ctor_get_uint8(v_toCbvSimprocOLeanEntry_2563_, sizeof(void*)*2);
v_keys_2567_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2563_, 1);
lean_inc_ref(v_keys_2567_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_2563_);
v___x_2568_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_2561_, v_keys_2567_, v_declName_2565_, v_phase_2566_, v_proc_2564_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2570_);
lean_inc_ref_n(v___x_2571_, 2);
v___x_2572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_ctor_set(v___x_2572_, 2, v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2573_, v_a_2574_);
lean_dec_ref(v_x_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___x_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_st_ref_get(v___x_2576_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___x_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2580_);
lean_dec(v___x_2580_);
return v_res_2582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___f_2592_; 
v___x_2591_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___f_2592_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2592_, 0, v___x_2591_);
return v___f_2592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___f_2593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2598_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___x_2600_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___f_2598_);
lean_ctor_set(v___x_2600_, 2, v___f_2597_);
lean_ctor_set(v___x_2600_, 3, v___f_2596_);
lean_ctor_set(v___x_2600_, 4, v___f_2595_);
lean_ctor_set(v___x_2600_, 5, v___f_2594_);
lean_ctor_set(v___x_2600_, 6, v___f_2593_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2603_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object* v_declName_2606_, lean_object* v_s_2607_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_2607_, v_declName_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2609_, lean_object* v_i_2610_, lean_object* v_k_2611_){
_start:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_array_get_size(v_keys_2609_);
v___x_2613_ = lean_nat_dec_lt(v_i_2610_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_dec(v_i_2610_);
return v___x_2613_;
}
else
{
lean_object* v_k_x27_2614_; uint8_t v___x_2615_; 
v_k_x27_2614_ = lean_array_fget_borrowed(v_keys_2609_, v_i_2610_);
v___x_2615_ = lean_name_eq(v_k_2611_, v_k_x27_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_i_2610_, v___x_2616_);
lean_dec(v_i_2610_);
v_i_2610_ = v___x_2617_;
goto _start;
}
else
{
lean_dec(v_i_2610_);
return v___x_2615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2619_, lean_object* v_i_2620_, lean_object* v_k_2621_){
_start:
{
uint8_t v_res_2622_; lean_object* v_r_2623_; 
v_res_2622_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2619_, v_i_2620_, v_k_2621_);
lean_dec(v_k_2621_);
lean_dec_ref(v_keys_2619_);
v_r_2623_ = lean_box(v_res_2622_);
return v_r_2623_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_2624_, size_t v_x_2625_, lean_object* v_x_2626_){
_start:
{
if (lean_obj_tag(v_x_2624_) == 0)
{
lean_object* v_es_2627_; lean_object* v___x_2628_; size_t v___x_2629_; size_t v___x_2630_; lean_object* v_j_2631_; lean_object* v___x_2632_; 
v_es_2627_ = lean_ctor_get(v_x_2624_, 0);
v___x_2628_ = lean_box(2);
v___x_2629_ = ((size_t)31ULL);
v___x_2630_ = lean_usize_land(v_x_2625_, v___x_2629_);
v_j_2631_ = lean_usize_to_nat(v___x_2630_);
v___x_2632_ = lean_array_get_borrowed(v___x_2628_, v_es_2627_, v_j_2631_);
lean_dec(v_j_2631_);
switch(lean_obj_tag(v___x_2632_))
{
case 0:
{
lean_object* v_key_2633_; uint8_t v___x_2634_; 
v_key_2633_ = lean_ctor_get(v___x_2632_, 0);
v___x_2634_ = lean_name_eq(v_x_2626_, v_key_2633_);
return v___x_2634_;
}
case 1:
{
lean_object* v_node_2635_; size_t v___x_2636_; size_t v___x_2637_; 
v_node_2635_ = lean_ctor_get(v___x_2632_, 0);
v___x_2636_ = ((size_t)5ULL);
v___x_2637_ = lean_usize_shift_right(v_x_2625_, v___x_2636_);
v_x_2624_ = v_node_2635_;
v_x_2625_ = v___x_2637_;
goto _start;
}
default: 
{
uint8_t v___x_2639_; 
v___x_2639_ = 0;
return v___x_2639_;
}
}
}
else
{
lean_object* v_ks_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v_ks_2640_ = lean_ctor_get(v_x_2624_, 0);
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_2640_, v___x_2641_, v_x_2626_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
size_t v_x_547__boxed_2646_; uint8_t v_res_2647_; lean_object* v_r_2648_; 
v_x_547__boxed_2646_ = lean_unbox_usize(v_x_2644_);
lean_dec(v_x_2644_);
v_res_2647_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2643_, v_x_547__boxed_2646_, v_x_2645_);
lean_dec(v_x_2645_);
lean_dec_ref(v_x_2643_);
v_r_2648_ = lean_box(v_res_2647_);
return v_r_2648_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
uint64_t v___y_2652_; 
if (lean_obj_tag(v_x_2650_) == 0)
{
uint64_t v___x_2655_; 
v___x_2655_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2652_ = v___x_2655_;
goto v___jp_2651_;
}
else
{
uint64_t v_hash_2656_; 
v_hash_2656_ = lean_ctor_get_uint64(v_x_2650_, sizeof(void*)*2);
v___y_2652_ = v_hash_2656_;
goto v___jp_2651_;
}
v___jp_2651_:
{
size_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = lean_uint64_to_usize(v___y_2652_);
v___x_2654_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2649_, v___x_2653_, v_x_2650_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_2657_, lean_object* v_x_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2657_, v_x_2658_);
lean_dec(v_x_2658_);
lean_dec_ref(v_x_2657_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1));
v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object* v_declName_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v_env_2671_; lean_object* v___x_2672_; lean_object* v_ext_2673_; lean_object* v_toEnvExtension_2674_; lean_object* v_asyncMode_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v_simprocNames_2678_; lean_object* v___f_2679_; lean_object* v___y_2681_; uint8_t v___x_2704_; 
v___x_2670_ = lean_st_ref_get(v_a_2668_);
v_env_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_ref(v_env_2671_);
lean_dec(v___x_2670_);
v___x_2672_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_2673_ = lean_ctor_get(v___x_2672_, 1);
v_toEnvExtension_2674_ = lean_ctor_get(v_ext_2673_, 0);
v_asyncMode_2675_ = lean_ctor_get(v_toEnvExtension_2674_, 2);
v___x_2676_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_2677_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2676_, v___x_2672_, v_env_2671_, v_asyncMode_2675_);
v_simprocNames_2678_ = lean_ctor_get(v___x_2677_, 3);
lean_inc_ref(v_simprocNames_2678_);
lean_dec(v___x_2677_);
lean_inc(v_declName_2666_);
v___f_2679_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_2679_, 0, v_declName_2666_);
v___x_2704_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_2678_, v_declName_2666_);
lean_dec_ref(v_simprocNames_2678_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec_ref(v___f_2679_);
v___x_2705_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0);
v___x_2706_ = l_Lean_MessageData_ofConstName(v_declName_2666_, v___x_2704_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2709_, v_a_2667_, v_a_2668_);
return v___x_2710_;
}
else
{
lean_dec(v_declName_2666_);
v___y_2681_ = v_a_2668_;
goto v___jp_2680_;
}
v___jp_2680_:
{
lean_object* v___x_2682_; lean_object* v_env_2683_; lean_object* v_nextMacroScope_2684_; lean_object* v_ngen_2685_; lean_object* v_auxDeclNGen_2686_; lean_object* v_traceState_2687_; lean_object* v_messages_2688_; lean_object* v_infoState_2689_; lean_object* v_snapshotTasks_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2702_; 
v___x_2682_ = lean_st_ref_take(v___y_2681_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
v_nextMacroScope_2684_ = lean_ctor_get(v___x_2682_, 1);
v_ngen_2685_ = lean_ctor_get(v___x_2682_, 2);
v_auxDeclNGen_2686_ = lean_ctor_get(v___x_2682_, 3);
v_traceState_2687_ = lean_ctor_get(v___x_2682_, 4);
v_messages_2688_ = lean_ctor_get(v___x_2682_, 6);
v_infoState_2689_ = lean_ctor_get(v___x_2682_, 7);
v_snapshotTasks_2690_ = lean_ctor_get(v___x_2682_, 8);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2682_, 5);
lean_dec(v_unused_2703_);
v___x_2692_ = v___x_2682_;
v_isShared_2693_ = v_isSharedCheck_2702_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_snapshotTasks_2690_);
lean_inc(v_infoState_2689_);
lean_inc(v_messages_2688_);
lean_inc(v_traceState_2687_);
lean_inc(v_auxDeclNGen_2686_);
lean_inc(v_ngen_2685_);
lean_inc(v_nextMacroScope_2684_);
lean_inc(v_env_2683_);
lean_dec(v___x_2682_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2702_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2694_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2672_, v_env_2683_, v___f_2679_);
v___x_2695_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 5, v___x_2695_);
lean_ctor_set(v___x_2692_, 0, v___x_2694_);
v___x_2697_ = v___x_2692_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_nextMacroScope_2684_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_ngen_2685_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_auxDeclNGen_2686_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_traceState_2687_);
lean_ctor_set(v_reuseFailAlloc_2701_, 5, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2701_, 6, v_messages_2688_);
lean_ctor_set(v_reuseFailAlloc_2701_, 7, v_infoState_2689_);
lean_ctor_set(v_reuseFailAlloc_2701_, 8, v_snapshotTasks_2690_);
v___x_2697_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_st_ref_set(v___y_2681_, v___x_2697_);
v___x_2699_ = lean_box(0);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object* v_declName_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object* v_00_u03b2_2716_, lean_object* v_x_2717_, lean_object* v_x_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2717_, v_x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(v_00_u03b2_2720_, v_x_2721_, v_x_2722_);
lean_dec(v_x_2722_);
lean_dec_ref(v_x_2721_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_2725_, lean_object* v_x_2726_, size_t v_x_2727_, lean_object* v_x_2728_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2726_, v_x_2727_, v_x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v_x_2733_){
_start:
{
size_t v_x_698__boxed_2734_; uint8_t v_res_2735_; lean_object* v_r_2736_; 
v_x_698__boxed_2734_ = lean_unbox_usize(v_x_2732_);
lean_dec(v_x_2732_);
v_res_2735_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_2730_, v_x_2731_, v_x_698__boxed_2734_, v_x_2733_);
lean_dec(v_x_2733_);
lean_dec_ref(v_x_2731_);
v_r_2736_ = lean_box(v_res_2735_);
return v_r_2736_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2737_, lean_object* v_keys_2738_, lean_object* v_vals_2739_, lean_object* v_heq_2740_, lean_object* v_i_2741_, lean_object* v_k_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2738_, v_i_2741_, v_k_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2744_, lean_object* v_keys_2745_, lean_object* v_vals_2746_, lean_object* v_heq_2747_, lean_object* v_i_2748_, lean_object* v_k_2749_){
_start:
{
uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_res_2750_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_2744_, v_keys_2745_, v_vals_2746_, v_heq_2747_, v_i_2748_, v_k_2749_);
lean_dec(v_k_2749_);
lean_dec_ref(v_vals_2746_);
lean_dec_ref(v_keys_2745_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object* v_ext_2752_, lean_object* v_b_2753_, uint8_t v_kind_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_currNamespace_2758_; lean_object* v___x_2759_; lean_object* v_env_2760_; lean_object* v_nextMacroScope_2761_; lean_object* v_ngen_2762_; lean_object* v_auxDeclNGen_2763_; lean_object* v_traceState_2764_; lean_object* v_messages_2765_; lean_object* v_infoState_2766_; lean_object* v_snapshotTasks_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2779_; 
v_currNamespace_2758_ = lean_ctor_get(v___y_2755_, 6);
v___x_2759_ = lean_st_ref_take(v___y_2756_);
v_env_2760_ = lean_ctor_get(v___x_2759_, 0);
v_nextMacroScope_2761_ = lean_ctor_get(v___x_2759_, 1);
v_ngen_2762_ = lean_ctor_get(v___x_2759_, 2);
v_auxDeclNGen_2763_ = lean_ctor_get(v___x_2759_, 3);
v_traceState_2764_ = lean_ctor_get(v___x_2759_, 4);
v_messages_2765_ = lean_ctor_get(v___x_2759_, 6);
v_infoState_2766_ = lean_ctor_get(v___x_2759_, 7);
v_snapshotTasks_2767_ = lean_ctor_get(v___x_2759_, 8);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v___x_2759_, 5);
lean_dec(v_unused_2780_);
v___x_2769_ = v___x_2759_;
v_isShared_2770_ = v_isSharedCheck_2779_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_snapshotTasks_2767_);
lean_inc(v_infoState_2766_);
lean_inc(v_messages_2765_);
lean_inc(v_traceState_2764_);
lean_inc(v_auxDeclNGen_2763_);
lean_inc(v_ngen_2762_);
lean_inc(v_nextMacroScope_2761_);
lean_inc(v_env_2760_);
lean_dec(v___x_2759_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2779_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_inc(v_currNamespace_2758_);
v___x_2771_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2760_, v_ext_2752_, v_b_2753_, v_kind_2754_, v_currNamespace_2758_);
v___x_2772_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 5, v___x_2772_);
lean_ctor_set(v___x_2769_, 0, v___x_2771_);
v___x_2774_ = v___x_2769_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextMacroScope_2761_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_ngen_2762_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_auxDeclNGen_2763_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v_traceState_2764_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_messages_2765_);
lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_infoState_2766_);
lean_ctor_set(v_reuseFailAlloc_2778_, 8, v_snapshotTasks_2767_);
v___x_2774_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2775_ = lean_st_ref_set(v___y_2756_, v___x_2774_);
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_2781_, lean_object* v_b_2782_, lean_object* v_kind_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
uint8_t v_kind_boxed_2787_; lean_object* v_res_2788_; 
v_kind_boxed_2787_ = lean_unbox(v_kind_2783_);
v_res_2788_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2781_, v_b_2782_, v_kind_boxed_2787_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object* v_00_u03b1_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_00_u03c3_2791_, lean_object* v_ext_2792_, lean_object* v_b_2793_, uint8_t v_kind_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2792_, v_b_2793_, v_kind_2794_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_2799_, lean_object* v_00_u03b2_2800_, lean_object* v_00_u03c3_2801_, lean_object* v_ext_2802_, lean_object* v_b_2803_, lean_object* v_kind_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v_kind_boxed_2808_; lean_object* v_res_2809_; 
v_kind_boxed_2808_ = lean_unbox(v_kind_2804_);
v_res_2809_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(v_00_u03b1_2799_, v_00_u03b2_2800_, v_00_u03c3_2801_, v_ext_2802_, v_b_2803_, v_kind_boxed_2808_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2809_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object* v_declName_2816_, uint8_t v_kind_2817_, uint8_t v_phase_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v_options_2824_; lean_object* v_ref_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2822_ = lean_st_ref_get(v_a_2820_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc_ref(v_env_2823_);
lean_dec(v___x_2822_);
v_options_2824_ = lean_ctor_get(v_a_2819_, 2);
v_ref_2825_ = lean_ctor_get(v_a_2819_, 5);
lean_inc_ref(v_options_2824_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_env_2823_);
lean_ctor_set(v___x_2826_, 1, v_options_2824_);
lean_inc(v_declName_2816_);
v___x_2827_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2816_, v___x_2826_);
lean_dec_ref_known(v___x_2826_, 2);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v_a_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
lean_inc(v_declName_2816_);
v___x_2829_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2816_, v_a_2820_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref(v___x_2829_);
if (lean_obj_tag(v_a_2830_) == 1)
{
lean_object* v_val_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_val_2831_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v_a_2830_, 1);
v___x_2832_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v___x_2833_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2833_, 0, v_declName_2816_);
lean_ctor_set(v___x_2833_, 1, v_val_2831_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*2, v_phase_2818_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set(v___x_2834_, 1, v_a_2828_);
v___x_2835_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_2832_, v___x_2834_, v_kind_2817_, v_a_2819_, v_a_2820_);
return v___x_2835_;
}
else
{
lean_object* v___x_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec(v_a_2830_);
lean_dec(v_a_2828_);
v___x_2836_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1);
v___x_2837_ = 0;
v___x_2838_ = l_Lean_MessageData_ofConstName(v_declName_2816_, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2836_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2841_, v_a_2819_, v_a_2820_);
return v___x_2842_;
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_declName_2816_);
v_a_2843_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2845_ = v___x_2827_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2827_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2847_ = lean_io_error_to_string(v_a_2843_);
v___x_2848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
v___x_2849_ = l_Lean_MessageData_ofFormat(v___x_2848_);
lean_inc(v_ref_2825_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_ref_2825_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2850_);
v___x_2852_ = v___x_2845_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object* v_declName_2855_, lean_object* v_kind_2856_, lean_object* v_phase_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
uint8_t v_kind_boxed_2861_; uint8_t v_phase_boxed_2862_; lean_object* v_res_2863_; 
v_kind_boxed_2861_ = lean_unbox(v_kind_2856_);
v_phase_boxed_2862_ = lean_unbox(v_phase_2857_);
v_res_2863_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2855_, v_kind_boxed_2861_, v_phase_boxed_2862_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2863_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object* v_stx_2876_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = l_Lean_Syntax_isNone(v_stx_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v_inner_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2878_ = lean_unsigned_to_nat(0u);
v_inner_2879_ = l_Lean_Syntax_getArg(v_stx_2876_, v___x_2878_);
v___x_2880_ = l_Lean_Syntax_getKind(v_inner_2879_);
v___x_2881_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2));
v___x_2882_ = lean_name_eq(v___x_2880_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2883_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4));
v___x_2884_ = lean_name_eq(v___x_2880_, v___x_2883_);
lean_dec(v___x_2880_);
if (v___x_2884_ == 0)
{
uint8_t v___x_2885_; 
v___x_2885_ = 2;
return v___x_2885_;
}
else
{
uint8_t v___x_2886_; 
v___x_2886_ = 1;
return v___x_2886_;
}
}
else
{
uint8_t v___x_2887_; 
lean_dec(v___x_2880_);
v___x_2887_ = 0;
return v___x_2887_;
}
}
else
{
uint8_t v___x_2888_; 
v___x_2888_ = 2;
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object* v_stx_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_2889_);
lean_dec(v_stx_2889_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2896_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
lean_ctor_set(v___x_2896_, 2, v___x_2895_);
lean_ctor_set(v___x_2896_, 3, v___x_2895_);
lean_ctor_set(v___x_2896_, 4, v___x_2895_);
lean_ctor_set(v___x_2896_, 5, v___x_2895_);
return v___x_2896_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_unsigned_to_nat(32u);
v___x_2898_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4(void){
_start:
{
size_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2900_ = ((size_t)5ULL);
v___x_2901_ = lean_unsigned_to_nat(0u);
v___x_2902_ = lean_unsigned_to_nat(32u);
v___x_2903_ = lean_mk_empty_array_with_capacity(v___x_2902_);
v___x_2904_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3);
v___x_2905_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v___x_2903_);
lean_ctor_set(v___x_2905_, 2, v___x_2901_);
lean_ctor_set(v___x_2905_, 3, v___x_2901_);
lean_ctor_set_usize(v___x_2905_, 4, v___x_2900_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
lean_ctor_set(v___x_2907_, 3, v___x_2906_);
lean_ctor_set(v___x_2907_, 4, v___x_2906_);
return v___x_2907_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2908_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5);
v___x_2909_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4);
v___x_2910_ = lean_box(1);
v___x_2911_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2);
v___x_2912_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v___x_2911_);
lean_ctor_set(v___x_2913_, 2, v___x_2910_);
lean_ctor_set(v___x_2913_, 3, v___x_2909_);
lean_ctor_set(v___x_2913_, 4, v___x_2908_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object* v_declName_2914_, lean_object* v_stx_2915_, uint8_t v_attrKind_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1));
lean_inc(v_declName_2914_);
v___x_2921_ = l_Lean_ensureAttrDeclIsMeta(v___x_2920_, v_declName_2914_, v_attrKind_2916_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; 
lean_dec_ref_known(v___x_2921_, 1);
v___x_2922_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_2923_ = lean_st_mk_ref(v___x_2922_);
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = l_Lean_Syntax_getArg(v_stx_2915_, v___x_2924_);
v___x_2926_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_2925_);
lean_dec(v___x_2925_);
v___x_2927_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2914_, v_attrKind_2916_, v___x_2926_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2936_; 
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2936_ == 0)
{
lean_object* v_unused_2937_; 
v_unused_2937_ = lean_ctor_get(v___x_2927_, 0);
lean_dec(v_unused_2937_);
v___x_2929_ = v___x_2927_;
v_isShared_2930_ = v_isSharedCheck_2936_;
goto v_resetjp_2928_;
}
else
{
lean_dec(v___x_2927_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2936_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2931_ = lean_st_ref_get(v___x_2923_);
lean_dec(v___x_2923_);
lean_dec(v___x_2931_);
v___x_2932_ = lean_box(0);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2932_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
else
{
lean_dec(v___x_2923_);
return v___x_2927_;
}
}
else
{
lean_dec(v_declName_2914_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object* v_declName_2938_, lean_object* v_stx_2939_, lean_object* v_attrKind_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
uint8_t v_attrKind_boxed_2944_; lean_object* v_res_2945_; 
v_attrKind_boxed_2944_ = lean_unbox(v_attrKind_2940_);
v_res_2945_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_2938_, v_stx_2939_, v_attrKind_boxed_2944_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_stx_2939_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object* v_ref_2948_, lean_object* v_declName_2949_, uint8_t v_phase_2950_, lean_object* v_proc_2951_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_keys_2955_; lean_object* v___x_2956_; 
v___x_2953_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_2954_ = lean_st_ref_get(v___x_2953_);
v_keys_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_ref(v_keys_2955_);
lean_dec(v___x_2954_);
v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_2955_, v_declName_2949_);
lean_dec_ref(v_keys_2955_);
if (lean_obj_tag(v___x_2956_) == 1)
{
lean_object* v_val_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2967_; 
v_val_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2967_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_val_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2967_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2961_ = lean_st_ref_take(v_ref_2948_);
v___x_2962_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v___x_2961_, v_val_2957_, v_declName_2949_, v_phase_2950_, v_proc_2951_);
v___x_2963_ = lean_st_ref_set(v_ref_2948_, v___x_2962_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2963_);
v___x_2965_ = v___x_2959_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec(v___x_2956_);
lean_dec_ref(v_proc_2951_);
v___x_2968_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0));
v___x_2969_ = l_Lean_privateToUserName(v_declName_2949_);
v___x_2970_ = 1;
v___x_2971_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_string_append(v___x_2968_, v___x_2971_);
lean_dec_ref(v___x_2971_);
v___x_2973_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1));
v___x_2974_ = lean_string_append(v___x_2972_, v___x_2973_);
v___x_2975_ = lean_mk_io_user_error(v___x_2974_);
v___x_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object* v_ref_2977_, lean_object* v_declName_2978_, lean_object* v_phase_2979_, lean_object* v_proc_2980_, lean_object* v_a_2981_){
_start:
{
uint8_t v_phase_boxed_2982_; lean_object* v_res_2983_; 
v_phase_boxed_2982_ = lean_unbox(v_phase_2979_);
v_res_2983_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_2977_, v_declName_2978_, v_phase_boxed_2982_, v_proc_2980_);
lean_dec(v_ref_2977_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object* v_declName_2984_, uint8_t v_phase_2985_, lean_object* v_proc_2986_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___x_2989_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v___x_2988_, v_declName_2984_, v_phase_2985_, v_proc_2986_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object* v_declName_2990_, lean_object* v_phase_2991_, lean_object* v_proc_2992_, lean_object* v_a_2993_){
_start:
{
uint8_t v_phase_boxed_2994_; lean_object* v_res_2995_; 
v_phase_boxed_2994_ = lean_unbox(v_phase_2991_);
v_res_2995_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_2990_, v_phase_boxed_2994_, v_proc_2992_);
return v_res_2995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_box(0);
v___x_3004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1));
v___x_3005_ = l_Lean_mkConst(v___x_3004_, v___x_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object* v_declName_3009_, lean_object* v_stx_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v_phase_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___y_3021_; 
v___x_3014_ = lean_unsigned_to_nat(1u);
v___x_3015_ = l_Lean_Syntax_getArg(v_stx_3010_, v___x_3014_);
v_phase_3016_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_3015_);
lean_dec(v___x_3015_);
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
lean_inc(v_declName_3009_);
v___x_3019_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3009_);
switch(v_phase_3016_)
{
case 0:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
v___y_3021_ = v___x_3053_;
goto v___jp_3020_;
}
case 1:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
v___y_3021_ = v___x_3054_;
goto v___jp_3020_;
}
default: 
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
v___y_3021_ = v___x_3055_;
goto v___jp_3020_;
}
}
v___jp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3022_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_3023_ = lean_st_mk_ref(v___x_3022_);
lean_inc(v_declName_3009_);
v___x_3024_ = l_Lean_mkConst(v_declName_3009_, v___x_3017_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4));
v___x_3026_ = l_Lean_Name_append(v_declName_3009_, v___x_3025_);
v___x_3027_ = l_Lean_Core_mkFreshUserName(v___x_3026_, v_a_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_val_3034_; lean_object* v___x_3035_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3029_ = lean_unsigned_to_nat(3u);
v___x_3030_ = lean_mk_empty_array_with_capacity(v___x_3029_);
v___x_3031_ = lean_array_push(v___x_3030_, v___x_3019_);
lean_inc_ref(v___y_3021_);
v___x_3032_ = lean_array_push(v___x_3031_, v___y_3021_);
v___x_3033_ = lean_array_push(v___x_3032_, v___x_3024_);
v_val_3034_ = l_Lean_mkAppN(v___x_3018_, v___x_3033_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = l_Lean_declareBuiltin(v_a_3028_, v_val_3034_, v_a_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3044_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3044_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3044_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3040_ = lean_st_ref_get(v___x_3023_);
lean_dec(v___x_3023_);
lean_dec(v___x_3040_);
if (v_isShared_3039_ == 0)
{
v___x_3042_ = v___x_3038_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3036_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
else
{
lean_dec(v___x_3023_);
return v___x_3035_;
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref(v___x_3024_);
lean_dec(v___x_3023_);
lean_dec_ref(v___x_3019_);
v_a_3045_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3027_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3027_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object* v_declName_3056_, lean_object* v_stx_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3056_, v_stx_3057_, v_a_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_stx_3057_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3148_ = l_Lean_registerBuiltinAttribute(v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_declName_3151_, lean_object* v_stx_3152_, uint8_t v_x_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3151_, v_stx_3152_, v___y_3154_, v___y_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_declName_3158_, lean_object* v_stx_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_x_116__boxed_3164_; lean_object* v_res_3165_; 
v_x_116__boxed_3164_ = lean_unbox(v_x_3160_);
v_res_3165_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3158_, v_stx_3159_, v_x_116__boxed_3164_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v_stx_3159_);
return v_res_3165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3168_ = l_Lean_stringToMessageData(v___x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_x_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3174_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3173_, v___y_3170_, v___y_3171_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v_x_3175_);
return v_res_3179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_unsigned_to_nat(3124561870u);
v___x_3183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3184_ = l_Lean_Name_num___override(v___x_3183_, v___x_3182_);
return v___x_3184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3187_ = l_Lean_Name_str___override(v___x_3186_, v___x_3185_);
return v___x_3187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3190_ = l_Lean_Name_str___override(v___x_3189_, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_unsigned_to_nat(2u);
v___x_3192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3193_ = l_Lean_Name_num___override(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3198_ = 1;
v___x_3199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3202_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3200_);
lean_ctor_set(v___x_3202_, 2, v___x_3199_);
lean_ctor_set_uint8(v___x_3202_, sizeof(void*)*3, v___x_3198_);
return v___x_3202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___f_3203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___f_3204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___f_3204_);
lean_ctor_set(v___x_3206_, 2, v___f_3203_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3209_ = l_Lean_registerBuiltinAttribute(v___x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object* v_a_3212_){
_start:
{
lean_object* v___x_3214_; lean_object* v_env_3215_; lean_object* v___x_3216_; lean_object* v_ext_3217_; lean_object* v_toEnvExtension_3218_; lean_object* v_asyncMode_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3214_ = lean_st_ref_get(v_a_3212_);
v_env_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_env_3215_);
lean_dec(v___x_3214_);
v___x_3216_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_3217_ = lean_ctor_get(v___x_3216_, 1);
v_toEnvExtension_3218_ = lean_ctor_get(v_ext_3217_, 0);
v_asyncMode_3219_ = lean_ctor_get(v_toEnvExtension_3218_, 2);
v___x_3220_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_3221_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3220_, v___x_3216_, v_env_3215_, v_asyncMode_3219_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3223_);
lean_dec(v_a_3223_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3230_, v_a_3231_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
return v_res_3233_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_unsigned_to_nat(32u);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3234_);
v___x_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3237_ = ((size_t)5ULL);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = lean_unsigned_to_nat(32u);
v___x_3240_ = lean_mk_empty_array_with_capacity(v___x_3239_);
v___x_3241_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0);
v___x_3242_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v___x_3240_);
lean_ctor_set(v___x_3242_, 2, v___x_3238_);
lean_ctor_set(v___x_3242_, 3, v___x_3238_);
lean_ctor_set_usize(v___x_3242_, 4, v___x_3237_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; lean_object* v_traceState_3246_; lean_object* v_traces_3247_; lean_object* v___x_3248_; lean_object* v_traceState_3249_; lean_object* v_env_3250_; lean_object* v_nextMacroScope_3251_; lean_object* v_ngen_3252_; lean_object* v_auxDeclNGen_3253_; lean_object* v_cache_3254_; lean_object* v_messages_3255_; lean_object* v_infoState_3256_; lean_object* v_snapshotTasks_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3276_; 
v___x_3245_ = lean_st_ref_get(v___y_3243_);
v_traceState_3246_ = lean_ctor_get(v___x_3245_, 4);
lean_inc_ref(v_traceState_3246_);
lean_dec(v___x_3245_);
v_traces_3247_ = lean_ctor_get(v_traceState_3246_, 0);
lean_inc_ref(v_traces_3247_);
lean_dec_ref(v_traceState_3246_);
v___x_3248_ = lean_st_ref_take(v___y_3243_);
v_traceState_3249_ = lean_ctor_get(v___x_3248_, 4);
v_env_3250_ = lean_ctor_get(v___x_3248_, 0);
v_nextMacroScope_3251_ = lean_ctor_get(v___x_3248_, 1);
v_ngen_3252_ = lean_ctor_get(v___x_3248_, 2);
v_auxDeclNGen_3253_ = lean_ctor_get(v___x_3248_, 3);
v_cache_3254_ = lean_ctor_get(v___x_3248_, 5);
v_messages_3255_ = lean_ctor_get(v___x_3248_, 6);
v_infoState_3256_ = lean_ctor_get(v___x_3248_, 7);
v_snapshotTasks_3257_ = lean_ctor_get(v___x_3248_, 8);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3259_ = v___x_3248_;
v_isShared_3260_ = v_isSharedCheck_3276_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_snapshotTasks_3257_);
lean_inc(v_infoState_3256_);
lean_inc(v_messages_3255_);
lean_inc(v_cache_3254_);
lean_inc(v_traceState_3249_);
lean_inc(v_auxDeclNGen_3253_);
lean_inc(v_ngen_3252_);
lean_inc(v_nextMacroScope_3251_);
lean_inc(v_env_3250_);
lean_dec(v___x_3248_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3276_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
uint64_t v_tid_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3274_; 
v_tid_3261_ = lean_ctor_get_uint64(v_traceState_3249_, sizeof(void*)*1);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_traceState_3249_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; 
v_unused_3275_ = lean_ctor_get(v_traceState_3249_, 0);
lean_dec(v_unused_3275_);
v___x_3263_ = v_traceState_3249_;
v_isShared_3264_ = v_isSharedCheck_3274_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v_traceState_3249_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3274_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3265_);
lean_ctor_set_uint64(v_reuseFailAlloc_3273_, sizeof(void*)*1, v_tid_3261_);
v___x_3267_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3269_; 
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 4, v___x_3267_);
v___x_3269_ = v___x_3259_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_env_3250_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_nextMacroScope_3251_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_ngen_3252_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_auxDeclNGen_3253_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3272_, 5, v_cache_3254_);
lean_ctor_set(v_reuseFailAlloc_3272_, 6, v_messages_3255_);
lean_ctor_set(v_reuseFailAlloc_3272_, 7, v_infoState_3256_);
lean_ctor_set(v_reuseFailAlloc_3272_, 8, v_snapshotTasks_3257_);
v___x_3269_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_st_ref_set(v___y_3243_, v___x_3269_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_traces_3247_);
return v___x_3271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3277_);
lean_dec(v___y_3277_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
return v_res_3301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object* v_opts_3302_, lean_object* v_opt_3303_){
_start:
{
lean_object* v_name_3304_; lean_object* v_defValue_3305_; lean_object* v_map_3306_; lean_object* v___x_3307_; 
v_name_3304_ = lean_ctor_get(v_opt_3303_, 0);
v_defValue_3305_ = lean_ctor_get(v_opt_3303_, 1);
v_map_3306_ = lean_ctor_get(v_opts_3302_, 0);
v___x_3307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3306_, v_name_3304_);
if (lean_obj_tag(v___x_3307_) == 0)
{
uint8_t v___x_3308_; 
v___x_3308_ = lean_unbox(v_defValue_3305_);
return v___x_3308_;
}
else
{
lean_object* v_val_3309_; 
v_val_3309_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_val_3309_);
lean_dec_ref_known(v___x_3307_, 1);
if (lean_obj_tag(v_val_3309_) == 1)
{
uint8_t v_v_3310_; 
v_v_3310_ = lean_ctor_get_uint8(v_val_3309_, 0);
lean_dec_ref_known(v_val_3309_, 0);
return v_v_3310_;
}
else
{
uint8_t v___x_3311_; 
lean_dec(v_val_3309_);
v___x_3311_ = lean_unbox(v_defValue_3305_);
return v___x_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object* v_opts_3312_, lean_object* v_opt_3313_){
_start:
{
uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_res_3314_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3312_, v_opt_3313_);
lean_dec_ref(v_opt_3313_);
lean_dec_ref(v_opts_3312_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t v___x_3316_, lean_object* v_e_3317_, lean_object* v_snd_3318_, lean_object* v_proc_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
if (v___x_3316_ == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_3317_, v_snd_3318_, v_proc_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; 
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
lean_inc(v___y_3326_);
lean_inc_ref(v___y_3325_);
lean_inc(v___y_3324_);
lean_inc_ref(v___y_3323_);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
lean_inc(v___y_3320_);
v___x_3331_ = lean_apply_11(v_proc_3319_, v_e_3317_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, lean_box(0));
return v___x_3331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object* v___x_3332_, lean_object* v_e_3333_, lean_object* v_snd_3334_, lean_object* v_proc_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v___x_48936__boxed_3346_; lean_object* v_res_3347_; 
v___x_48936__boxed_3346_ = lean_unbox(v___x_3332_);
v_res_3347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_48936__boxed_3346_, v_e_3333_, v_snd_3334_, v_proc_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec(v_snd_3334_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object* v_x_3348_){
_start:
{
if (lean_obj_tag(v_x_3348_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v_x_3348_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_x_3348_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v_x_3348_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v_x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 1);
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_a_3358_ = lean_ctor_get(v_x_3348_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_x_3348_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v_x_3348_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v_x_3348_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 0);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object* v_x_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t v_sz_3369_, size_t v_i_3370_, lean_object* v_bs_3371_){
_start:
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_usize_dec_lt(v_i_3370_, v_sz_3369_);
if (v___x_3372_ == 0)
{
return v_bs_3371_;
}
else
{
lean_object* v_v_3373_; lean_object* v_msg_3374_; lean_object* v___x_3375_; lean_object* v_bs_x27_3376_; size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v_v_3373_ = lean_array_uget_borrowed(v_bs_3371_, v_i_3370_);
v_msg_3374_ = lean_ctor_get(v_v_3373_, 1);
lean_inc_ref(v_msg_3374_);
v___x_3375_ = lean_unsigned_to_nat(0u);
v_bs_x27_3376_ = lean_array_uset(v_bs_3371_, v_i_3370_, v___x_3375_);
v___x_3377_ = ((size_t)1ULL);
v___x_3378_ = lean_usize_add(v_i_3370_, v___x_3377_);
v___x_3379_ = lean_array_uset(v_bs_x27_3376_, v_i_3370_, v_msg_3374_);
v_i_3370_ = v___x_3378_;
v_bs_3371_ = v___x_3379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_3381_, lean_object* v_i_3382_, lean_object* v_bs_3383_){
_start:
{
size_t v_sz_boxed_3384_; size_t v_i_boxed_3385_; lean_object* v_res_3386_; 
v_sz_boxed_3384_ = lean_unbox_usize(v_sz_3381_);
lean_dec(v_sz_3381_);
v_i_boxed_3385_ = lean_unbox_usize(v_i_3382_);
lean_dec(v_i_3382_);
v_res_3386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_boxed_3384_, v_i_boxed_3385_, v_bs_3383_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object* v_msgData_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___x_3393_; lean_object* v_env_3394_; lean_object* v___x_3395_; lean_object* v_mctx_3396_; lean_object* v_lctx_3397_; lean_object* v_options_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3393_ = lean_st_ref_get(v___y_3391_);
v_env_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc_ref(v_env_3394_);
lean_dec(v___x_3393_);
v___x_3395_ = lean_st_ref_get(v___y_3389_);
v_mctx_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc_ref(v_mctx_3396_);
lean_dec(v___x_3395_);
v_lctx_3397_ = lean_ctor_get(v___y_3388_, 2);
v_options_3398_ = lean_ctor_get(v___y_3390_, 2);
lean_inc_ref(v_options_3398_);
lean_inc_ref(v_lctx_3397_);
v___x_3399_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3399_, 0, v_env_3394_);
lean_ctor_set(v___x_3399_, 1, v_mctx_3396_);
lean_ctor_set(v___x_3399_, 2, v_lctx_3397_);
lean_ctor_set(v___x_3399_, 3, v_options_3398_);
v___x_3400_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v_msgData_3387_);
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msgData_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object* v_oldTraces_3409_, lean_object* v_data_3410_, lean_object* v_ref_3411_, lean_object* v_msg_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_fileName_3418_; lean_object* v_fileMap_3419_; lean_object* v_options_3420_; lean_object* v_currRecDepth_3421_; lean_object* v_maxRecDepth_3422_; lean_object* v_ref_3423_; lean_object* v_currNamespace_3424_; lean_object* v_openDecls_3425_; lean_object* v_initHeartbeats_3426_; lean_object* v_maxHeartbeats_3427_; lean_object* v_quotContext_3428_; lean_object* v_currMacroScope_3429_; uint8_t v_diag_3430_; lean_object* v_cancelTk_x3f_3431_; uint8_t v_suppressElabErrors_3432_; lean_object* v_inheritedTraceOptions_3433_; lean_object* v___x_3434_; lean_object* v_traceState_3435_; lean_object* v_traces_3436_; lean_object* v_ref_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; size_t v_sz_3440_; size_t v___x_3441_; lean_object* v___x_3442_; lean_object* v_msg_3443_; lean_object* v___x_3444_; lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3482_; 
v_fileName_3418_ = lean_ctor_get(v___y_3415_, 0);
v_fileMap_3419_ = lean_ctor_get(v___y_3415_, 1);
v_options_3420_ = lean_ctor_get(v___y_3415_, 2);
v_currRecDepth_3421_ = lean_ctor_get(v___y_3415_, 3);
v_maxRecDepth_3422_ = lean_ctor_get(v___y_3415_, 4);
v_ref_3423_ = lean_ctor_get(v___y_3415_, 5);
v_currNamespace_3424_ = lean_ctor_get(v___y_3415_, 6);
v_openDecls_3425_ = lean_ctor_get(v___y_3415_, 7);
v_initHeartbeats_3426_ = lean_ctor_get(v___y_3415_, 8);
v_maxHeartbeats_3427_ = lean_ctor_get(v___y_3415_, 9);
v_quotContext_3428_ = lean_ctor_get(v___y_3415_, 10);
v_currMacroScope_3429_ = lean_ctor_get(v___y_3415_, 11);
v_diag_3430_ = lean_ctor_get_uint8(v___y_3415_, sizeof(void*)*14);
v_cancelTk_x3f_3431_ = lean_ctor_get(v___y_3415_, 12);
v_suppressElabErrors_3432_ = lean_ctor_get_uint8(v___y_3415_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3433_ = lean_ctor_get(v___y_3415_, 13);
v___x_3434_ = lean_st_ref_get(v___y_3416_);
v_traceState_3435_ = lean_ctor_get(v___x_3434_, 4);
lean_inc_ref(v_traceState_3435_);
lean_dec(v___x_3434_);
v_traces_3436_ = lean_ctor_get(v_traceState_3435_, 0);
lean_inc_ref(v_traces_3436_);
lean_dec_ref(v_traceState_3435_);
v_ref_3437_ = l_Lean_replaceRef(v_ref_3411_, v_ref_3423_);
lean_inc_ref(v_inheritedTraceOptions_3433_);
lean_inc(v_cancelTk_x3f_3431_);
lean_inc(v_currMacroScope_3429_);
lean_inc(v_quotContext_3428_);
lean_inc(v_maxHeartbeats_3427_);
lean_inc(v_initHeartbeats_3426_);
lean_inc(v_openDecls_3425_);
lean_inc(v_currNamespace_3424_);
lean_inc(v_maxRecDepth_3422_);
lean_inc(v_currRecDepth_3421_);
lean_inc_ref(v_options_3420_);
lean_inc_ref(v_fileMap_3419_);
lean_inc_ref(v_fileName_3418_);
v___x_3438_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3438_, 0, v_fileName_3418_);
lean_ctor_set(v___x_3438_, 1, v_fileMap_3419_);
lean_ctor_set(v___x_3438_, 2, v_options_3420_);
lean_ctor_set(v___x_3438_, 3, v_currRecDepth_3421_);
lean_ctor_set(v___x_3438_, 4, v_maxRecDepth_3422_);
lean_ctor_set(v___x_3438_, 5, v_ref_3437_);
lean_ctor_set(v___x_3438_, 6, v_currNamespace_3424_);
lean_ctor_set(v___x_3438_, 7, v_openDecls_3425_);
lean_ctor_set(v___x_3438_, 8, v_initHeartbeats_3426_);
lean_ctor_set(v___x_3438_, 9, v_maxHeartbeats_3427_);
lean_ctor_set(v___x_3438_, 10, v_quotContext_3428_);
lean_ctor_set(v___x_3438_, 11, v_currMacroScope_3429_);
lean_ctor_set(v___x_3438_, 12, v_cancelTk_x3f_3431_);
lean_ctor_set(v___x_3438_, 13, v_inheritedTraceOptions_3433_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*14, v_diag_3430_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*14 + 1, v_suppressElabErrors_3432_);
v___x_3439_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3436_);
lean_dec_ref(v_traces_3436_);
v_sz_3440_ = lean_array_size(v___x_3439_);
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_3440_, v___x_3441_, v___x_3439_);
v_msg_3443_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3443_, 0, v_data_3410_);
lean_ctor_set(v_msg_3443_, 1, v_msg_3412_);
lean_ctor_set(v_msg_3443_, 2, v___x_3442_);
v___x_3444_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msg_3443_, v___y_3413_, v___y_3414_, v___x_3438_, v___y_3416_);
lean_dec_ref_known(v___x_3438_, 14);
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3482_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3482_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_traceState_3450_; lean_object* v_env_3451_; lean_object* v_nextMacroScope_3452_; lean_object* v_ngen_3453_; lean_object* v_auxDeclNGen_3454_; lean_object* v_cache_3455_; lean_object* v_messages_3456_; lean_object* v_infoState_3457_; lean_object* v_snapshotTasks_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3481_; 
v___x_3449_ = lean_st_ref_take(v___y_3416_);
v_traceState_3450_ = lean_ctor_get(v___x_3449_, 4);
v_env_3451_ = lean_ctor_get(v___x_3449_, 0);
v_nextMacroScope_3452_ = lean_ctor_get(v___x_3449_, 1);
v_ngen_3453_ = lean_ctor_get(v___x_3449_, 2);
v_auxDeclNGen_3454_ = lean_ctor_get(v___x_3449_, 3);
v_cache_3455_ = lean_ctor_get(v___x_3449_, 5);
v_messages_3456_ = lean_ctor_get(v___x_3449_, 6);
v_infoState_3457_ = lean_ctor_get(v___x_3449_, 7);
v_snapshotTasks_3458_ = lean_ctor_get(v___x_3449_, 8);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3460_ = v___x_3449_;
v_isShared_3461_ = v_isSharedCheck_3481_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_snapshotTasks_3458_);
lean_inc(v_infoState_3457_);
lean_inc(v_messages_3456_);
lean_inc(v_cache_3455_);
lean_inc(v_traceState_3450_);
lean_inc(v_auxDeclNGen_3454_);
lean_inc(v_ngen_3453_);
lean_inc(v_nextMacroScope_3452_);
lean_inc(v_env_3451_);
lean_dec(v___x_3449_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3481_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
uint64_t v_tid_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3479_; 
v_tid_3462_ = lean_ctor_get_uint64(v_traceState_3450_, sizeof(void*)*1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_traceState_3450_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v_traceState_3450_, 0);
lean_dec(v_unused_3480_);
v___x_3464_ = v_traceState_3450_;
v_isShared_3465_ = v_isSharedCheck_3479_;
goto v_resetjp_3463_;
}
else
{
lean_dec(v_traceState_3450_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3479_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_ref_3411_);
lean_ctor_set(v___x_3466_, 1, v_a_3445_);
v___x_3467_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3409_, v___x_3466_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3467_);
v___x_3469_ = v___x_3464_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3467_);
lean_ctor_set_uint64(v_reuseFailAlloc_3478_, sizeof(void*)*1, v_tid_3462_);
v___x_3469_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 4, v___x_3469_);
v___x_3471_ = v___x_3460_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_env_3451_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_nextMacroScope_3452_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_ngen_3453_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_auxDeclNGen_3454_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3477_, 5, v_cache_3455_);
lean_ctor_set(v_reuseFailAlloc_3477_, 6, v_messages_3456_);
lean_ctor_set(v_reuseFailAlloc_3477_, 7, v_infoState_3457_);
lean_ctor_set(v_reuseFailAlloc_3477_, 8, v_snapshotTasks_3458_);
v___x_3471_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3472_ = lean_st_ref_set(v___y_3416_, v___x_3471_);
v___x_3473_ = lean_box(0);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3473_);
v___x_3475_ = v___x_3447_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_3483_, lean_object* v_data_3484_, lean_object* v_ref_3485_, lean_object* v_msg_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3483_, v_data_3484_, v_ref_3485_, v_msg_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object* v_opts_3493_, lean_object* v_opt_3494_){
_start:
{
lean_object* v_name_3495_; lean_object* v_defValue_3496_; lean_object* v_map_3497_; lean_object* v___x_3498_; 
v_name_3495_ = lean_ctor_get(v_opt_3494_, 0);
v_defValue_3496_ = lean_ctor_get(v_opt_3494_, 1);
v_map_3497_ = lean_ctor_get(v_opts_3493_, 0);
v___x_3498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3497_, v_name_3495_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_inc(v_defValue_3496_);
return v_defValue_3496_;
}
else
{
lean_object* v_val_3499_; 
v_val_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v___x_3498_, 1);
if (lean_obj_tag(v_val_3499_) == 3)
{
lean_object* v_v_3500_; 
v_v_3500_ = lean_ctor_get(v_val_3499_, 0);
lean_inc(v_v_3500_);
lean_dec_ref_known(v_val_3499_, 1);
return v_v_3500_;
}
else
{
lean_dec(v_val_3499_);
lean_inc(v_defValue_3496_);
return v_defValue_3496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object* v_opts_3501_, lean_object* v_opt_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3501_, v_opt_3502_);
lean_dec_ref(v_opt_3502_);
lean_dec_ref(v_opts_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object* v_e_3504_){
_start:
{
if (lean_obj_tag(v_e_3504_) == 0)
{
uint8_t v___x_3505_; 
v___x_3505_ = 2;
return v___x_3505_;
}
else
{
uint8_t v___x_3506_; 
v___x_3506_ = 0;
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object* v_e_3507_){
_start:
{
uint8_t v_res_3508_; lean_object* v_r_3509_; 
v_res_3508_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_e_3507_);
lean_dec_ref(v_e_3507_);
v_r_3509_ = lean_box(v_res_3508_);
return v_r_3509_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3510_; double v___x_3511_; 
v___x_3510_ = lean_unsigned_to_nat(0u);
v___x_3511_ = lean_float_of_nat(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1));
v___x_3514_ = l_Lean_stringToMessageData(v___x_3513_);
return v___x_3514_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3515_; double v___x_3516_; 
v___x_3515_ = lean_unsigned_to_nat(1000u);
v___x_3516_ = lean_float_of_nat(v___x_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object* v_cls_3517_, uint8_t v_collapsed_3518_, lean_object* v_tag_3519_, lean_object* v_opts_3520_, uint8_t v_clsEnabled_3521_, lean_object* v_oldTraces_3522_, lean_object* v_msg_3523_, lean_object* v_resStartStop_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_fst_3535_; lean_object* v_snd_3536_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v_data_3540_; lean_object* v_fst_3551_; lean_object* v_snd_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; lean_object* v___y_3556_; lean_object* v_a_3557_; uint8_t v___y_3572_; double v___y_3603_; 
v_fst_3535_ = lean_ctor_get(v_resStartStop_3524_, 0);
lean_inc(v_fst_3535_);
v_snd_3536_ = lean_ctor_get(v_resStartStop_3524_, 1);
lean_inc(v_snd_3536_);
lean_dec_ref(v_resStartStop_3524_);
v_fst_3551_ = lean_ctor_get(v_snd_3536_, 0);
lean_inc(v_fst_3551_);
v_snd_3552_ = lean_ctor_get(v_snd_3536_, 1);
lean_inc(v_snd_3552_);
lean_dec(v_snd_3536_);
v___x_3553_ = l_Lean_trace_profiler;
v___x_3554_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3520_, v___x_3553_);
if (v___x_3554_ == 0)
{
v___y_3572_ = v___x_3554_;
goto v___jp_3571_;
}
else
{
lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3608_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3609_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3520_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; double v___x_3612_; double v___x_3613_; double v___x_3614_; 
v___x_3610_ = l_Lean_trace_profiler_threshold;
v___x_3611_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3520_, v___x_3610_);
v___x_3612_ = lean_float_of_nat(v___x_3611_);
v___x_3613_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3);
v___x_3614_ = lean_float_div(v___x_3612_, v___x_3613_);
v___y_3603_ = v___x_3614_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; double v___x_3617_; 
v___x_3615_ = l_Lean_trace_profiler_threshold;
v___x_3616_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3520_, v___x_3615_);
v___x_3617_ = lean_float_of_nat(v___x_3616_);
v___y_3603_ = v___x_3617_;
goto v___jp_3602_;
}
}
v___jp_3537_:
{
lean_object* v___x_3541_; 
lean_inc(v___y_3538_);
v___x_3541_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3522_, v_data_3540_, v___y_3538_, v___y_3539_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v___x_3542_; 
lean_dec_ref_known(v___x_3541_, 1);
v___x_3542_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3535_);
return v___x_3542_;
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_fst_3535_);
v_a_3543_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3541_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3541_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
v___jp_3555_:
{
uint8_t v_result_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; double v___x_3561_; lean_object* v_data_3562_; 
v_result_3558_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_fst_3535_);
v___x_3559_ = lean_box(v_result_3558_);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
v___x_3561_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0);
lean_inc_ref(v_tag_3519_);
lean_inc_ref(v___x_3560_);
lean_inc(v_cls_3517_);
v_data_3562_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3562_, 0, v_cls_3517_);
lean_ctor_set(v_data_3562_, 1, v___x_3560_);
lean_ctor_set(v_data_3562_, 2, v_tag_3519_);
lean_ctor_set_float(v_data_3562_, sizeof(void*)*3, v___x_3561_);
lean_ctor_set_float(v_data_3562_, sizeof(void*)*3 + 8, v___x_3561_);
lean_ctor_set_uint8(v_data_3562_, sizeof(void*)*3 + 16, v_collapsed_3518_);
if (v___x_3554_ == 0)
{
lean_dec_ref_known(v___x_3560_, 1);
lean_dec(v_snd_3552_);
lean_dec(v_fst_3551_);
lean_dec_ref(v_tag_3519_);
lean_dec(v_cls_3517_);
v___y_3538_ = v___y_3556_;
v___y_3539_ = v_a_3557_;
v_data_3540_ = v_data_3562_;
goto v___jp_3537_;
}
else
{
lean_object* v_data_3563_; double v___x_3564_; double v___x_3565_; 
lean_dec_ref_known(v_data_3562_, 3);
v_data_3563_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3563_, 0, v_cls_3517_);
lean_ctor_set(v_data_3563_, 1, v___x_3560_);
lean_ctor_set(v_data_3563_, 2, v_tag_3519_);
v___x_3564_ = lean_unbox_float(v_fst_3551_);
lean_dec(v_fst_3551_);
lean_ctor_set_float(v_data_3563_, sizeof(void*)*3, v___x_3564_);
v___x_3565_ = lean_unbox_float(v_snd_3552_);
lean_dec(v_snd_3552_);
lean_ctor_set_float(v_data_3563_, sizeof(void*)*3 + 8, v___x_3565_);
lean_ctor_set_uint8(v_data_3563_, sizeof(void*)*3 + 16, v_collapsed_3518_);
v___y_3538_ = v___y_3556_;
v___y_3539_ = v_a_3557_;
v_data_3540_ = v_data_3563_;
goto v___jp_3537_;
}
}
v___jp_3566_:
{
lean_object* v_ref_3567_; lean_object* v___x_3568_; 
v_ref_3567_ = lean_ctor_get(v___y_3532_, 5);
lean_inc(v___y_3533_);
lean_inc_ref(v___y_3532_);
lean_inc(v___y_3531_);
lean_inc_ref(v___y_3530_);
lean_inc(v___y_3529_);
lean_inc_ref(v___y_3528_);
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3526_);
lean_inc(v___y_3525_);
lean_inc(v_fst_3535_);
v___x_3568_ = lean_apply_11(v_msg_3523_, v_fst_3535_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, lean_box(0));
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v___y_3556_ = v_ref_3567_;
v_a_3557_ = v_a_3569_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3570_; 
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2);
v___y_3556_ = v_ref_3567_;
v_a_3557_ = v___x_3570_;
goto v___jp_3555_;
}
}
v___jp_3571_:
{
if (v_clsEnabled_3521_ == 0)
{
if (v___y_3572_ == 0)
{
lean_object* v___x_3573_; lean_object* v_traceState_3574_; lean_object* v_env_3575_; lean_object* v_nextMacroScope_3576_; lean_object* v_ngen_3577_; lean_object* v_auxDeclNGen_3578_; lean_object* v_cache_3579_; lean_object* v_messages_3580_; lean_object* v_infoState_3581_; lean_object* v_snapshotTasks_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_snd_3552_);
lean_dec(v_fst_3551_);
lean_dec_ref(v_msg_3523_);
lean_dec_ref(v_tag_3519_);
lean_dec(v_cls_3517_);
v___x_3573_ = lean_st_ref_take(v___y_3533_);
v_traceState_3574_ = lean_ctor_get(v___x_3573_, 4);
v_env_3575_ = lean_ctor_get(v___x_3573_, 0);
v_nextMacroScope_3576_ = lean_ctor_get(v___x_3573_, 1);
v_ngen_3577_ = lean_ctor_get(v___x_3573_, 2);
v_auxDeclNGen_3578_ = lean_ctor_get(v___x_3573_, 3);
v_cache_3579_ = lean_ctor_get(v___x_3573_, 5);
v_messages_3580_ = lean_ctor_get(v___x_3573_, 6);
v_infoState_3581_ = lean_ctor_get(v___x_3573_, 7);
v_snapshotTasks_3582_ = lean_ctor_get(v___x_3573_, 8);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3584_ = v___x_3573_;
v_isShared_3585_ = v_isSharedCheck_3601_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_snapshotTasks_3582_);
lean_inc(v_infoState_3581_);
lean_inc(v_messages_3580_);
lean_inc(v_cache_3579_);
lean_inc(v_traceState_3574_);
lean_inc(v_auxDeclNGen_3578_);
lean_inc(v_ngen_3577_);
lean_inc(v_nextMacroScope_3576_);
lean_inc(v_env_3575_);
lean_dec(v___x_3573_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3601_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
uint64_t v_tid_3586_; lean_object* v_traces_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3600_; 
v_tid_3586_ = lean_ctor_get_uint64(v_traceState_3574_, sizeof(void*)*1);
v_traces_3587_ = lean_ctor_get(v_traceState_3574_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_traceState_3574_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3589_ = v_traceState_3574_;
v_isShared_3590_ = v_isSharedCheck_3600_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_traces_3587_);
lean_dec(v_traceState_3574_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3600_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3522_, v_traces_3587_);
lean_dec_ref(v_traces_3587_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3591_);
v___x_3593_ = v___x_3589_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3591_);
lean_ctor_set_uint64(v_reuseFailAlloc_3599_, sizeof(void*)*1, v_tid_3586_);
v___x_3593_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3595_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v___x_3593_);
v___x_3595_ = v___x_3584_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_env_3575_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_nextMacroScope_3576_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_ngen_3577_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_auxDeclNGen_3578_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3598_, 5, v_cache_3579_);
lean_ctor_set(v_reuseFailAlloc_3598_, 6, v_messages_3580_);
lean_ctor_set(v_reuseFailAlloc_3598_, 7, v_infoState_3581_);
lean_ctor_set(v_reuseFailAlloc_3598_, 8, v_snapshotTasks_3582_);
v___x_3595_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_st_ref_set(v___y_3533_, v___x_3595_);
v___x_3597_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3535_);
return v___x_3597_;
}
}
}
}
}
else
{
goto v___jp_3566_;
}
}
else
{
goto v___jp_3566_;
}
}
v___jp_3602_:
{
double v___x_3604_; double v___x_3605_; double v___x_3606_; uint8_t v___x_3607_; 
v___x_3604_ = lean_unbox_float(v_snd_3552_);
v___x_3605_ = lean_unbox_float(v_fst_3551_);
v___x_3606_ = lean_float_sub(v___x_3604_, v___x_3605_);
v___x_3607_ = lean_float_decLt(v___y_3603_, v___x_3606_);
v___y_3572_ = v___x_3607_;
goto v___jp_3571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object** _args){
lean_object* v_cls_3618_ = _args[0];
lean_object* v_collapsed_3619_ = _args[1];
lean_object* v_tag_3620_ = _args[2];
lean_object* v_opts_3621_ = _args[3];
lean_object* v_clsEnabled_3622_ = _args[4];
lean_object* v_oldTraces_3623_ = _args[5];
lean_object* v_msg_3624_ = _args[6];
lean_object* v_resStartStop_3625_ = _args[7];
lean_object* v___y_3626_ = _args[8];
lean_object* v___y_3627_ = _args[9];
lean_object* v___y_3628_ = _args[10];
lean_object* v___y_3629_ = _args[11];
lean_object* v___y_3630_ = _args[12];
lean_object* v___y_3631_ = _args[13];
lean_object* v___y_3632_ = _args[14];
lean_object* v___y_3633_ = _args[15];
lean_object* v___y_3634_ = _args[16];
lean_object* v___y_3635_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3636_; uint8_t v_clsEnabled_boxed_3637_; lean_object* v_res_3638_; 
v_collapsed_boxed_3636_ = lean_unbox(v_collapsed_3619_);
v_clsEnabled_boxed_3637_ = lean_unbox(v_clsEnabled_3622_);
v_res_3638_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_3618_, v_collapsed_boxed_3636_, v_tag_3620_, v_opts_3621_, v_clsEnabled_boxed_3637_, v_oldTraces_3623_, v_msg_3624_, v_resStartStop_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v_opts_3621_);
return v_res_3638_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0));
v___x_3641_ = l_Lean_stringToMessageData(v___x_3640_);
return v___x_3641_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2));
v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4));
v___x_3647_ = l_Lean_stringToMessageData(v___x_3646_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object* v___x_3657_, lean_object* v_e_3658_, lean_object* v_x_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v_e_3658_);
v_a_3670_ = lean_ctor_get(v_x_3659_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_x_3659_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3672_ = v_x_3659_;
v_isShared_3673_ = v_isSharedCheck_3684_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v_x_3659_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3684_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3675_ = l_Lean_MessageData_ofName(v___x_3657_);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3);
v___x_3678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = l_Lean_Exception_toMessageData(v_a_3670_);
v___x_3680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3680_);
v___x_3682_ = v___x_3672_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3723_; 
v_a_3685_ = lean_ctor_get(v_x_3659_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v_x_3659_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3687_ = v_x_3659_;
v_isShared_3688_ = v_isSharedCheck_3723_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v_x_3659_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3723_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
if (lean_obj_tag(v_a_3685_) == 0)
{
uint8_t v_done_3689_; 
v_done_3689_ = lean_ctor_get_uint8(v_a_3685_, 0);
lean_dec_ref_known(v_a_3685_, 0);
if (v_done_3689_ == 1)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3691_ = l_Lean_MessageData_ofName(v___x_3657_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = l_Lean_indentExpr(v_e_3658_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3696_);
v___x_3698_ = v___x_3687_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_dec_ref(v_e_3658_);
v___x_3700_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3701_ = l_Lean_MessageData_ofName(v___x_3657_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3704_);
v___x_3706_ = v___x_3687_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
else
{
lean_object* v_e_x27_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
v_e_x27_3708_ = lean_ctor_get(v_a_3685_, 0);
lean_inc_ref(v_e_x27_3708_);
lean_dec_ref_known(v_a_3685_, 2);
v___x_3709_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3710_ = l_Lean_MessageData_ofName(v___x_3657_);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = l_Lean_indentExpr(v_e_3658_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = l_Lean_indentExpr(v_e_x27_3708_);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3719_);
v___x_3721_ = v___x_3687_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object* v___x_3724_, lean_object* v_e_3725_, lean_object* v_x_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_3724_, v_e_3725_, v_x_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
return v_res_3737_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8));
v___x_3764_ = l_Lean_Name_append(v___x_3763_, v___x_3762_);
return v___x_3764_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10(void){
_start:
{
lean_object* v___x_3765_; double v___x_3766_; 
v___x_3765_ = lean_unsigned_to_nat(1000000000u);
v___x_3766_ = lean_float_of_nat(v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object* v_erased_3767_, lean_object* v_e_3768_, lean_object* v_as_3769_, size_t v_sz_3770_, size_t v_i_3771_, lean_object* v_b_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_a_3784_; uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_lt(v_i_3771_, v_sz_3770_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v_e_3768_);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_b_3772_);
return v___x_3789_;
}
else
{
lean_object* v_a_3790_; lean_object* v_fst_3791_; lean_object* v_toCbvSimprocOLeanEntry_3792_; lean_object* v_snd_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v_b_3772_);
v_a_3790_ = lean_array_uget(v_as_3769_, v_i_3771_);
v_fst_3791_ = lean_ctor_get(v_a_3790_, 0);
lean_inc(v_fst_3791_);
v_toCbvSimprocOLeanEntry_3792_ = lean_ctor_get(v_fst_3791_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_3792_);
v_snd_3793_ = lean_ctor_get(v_a_3790_, 1);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_a_3790_);
if (v_isSharedCheck_3934_ == 0)
{
lean_object* v_unused_3935_; 
v_unused_3935_ = lean_ctor_get(v_a_3790_, 0);
lean_dec(v_unused_3935_);
v___x_3795_ = v_a_3790_;
v_isShared_3796_ = v_isSharedCheck_3934_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_snd_3793_);
lean_dec(v_a_3790_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3934_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v_proc_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3932_; 
v_proc_3797_ = lean_ctor_get(v_fst_3791_, 1);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_fst_3791_);
if (v_isSharedCheck_3932_ == 0)
{
lean_object* v_unused_3933_; 
v_unused_3933_ = lean_ctor_get(v_fst_3791_, 0);
lean_dec(v_unused_3933_);
v___x_3799_ = v_fst_3791_;
v_isShared_3800_ = v_isSharedCheck_3932_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_proc_3797_);
lean_dec(v_fst_3791_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3932_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_declName_3801_; lean_object* v___x_3802_; lean_object* v___y_3804_; lean_object* v___x_3810_; uint8_t v___x_3811_; lean_object* v___y_3813_; 
v_declName_3801_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_3792_, 0);
lean_inc(v_declName_3801_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_3792_);
v___x_3802_ = lean_box(0);
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v___x_3811_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_3767_, v_declName_3801_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3836_; lean_object* v_options_3837_; lean_object* v_inheritedTraceOptions_3838_; uint8_t v_hasTrace_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v___x_3836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1));
v_options_3837_ = lean_ctor_get(v___y_3780_, 2);
v_inheritedTraceOptions_3838_ = lean_ctor_get(v___y_3780_, 13);
v_hasTrace_3839_ = lean_ctor_get_uint8(v_options_3837_, sizeof(void*)*1);
v___x_3840_ = lean_unsigned_to_nat(0u);
v___x_3841_ = lean_nat_dec_eq(v_snd_3793_, v___x_3840_);
if (v_hasTrace_3839_ == 0)
{
lean_object* v___x_3842_; 
lean_dec(v_declName_3801_);
lean_inc_ref(v_e_3768_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3841_, v_e_3768_, v_snd_3793_, v_proc_3797_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v_snd_3793_);
v___y_3813_ = v___x_3842_;
goto v___jp_3812_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v_a_3856_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v_a_3871_; 
v___x_3843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2));
v___x_3844_ = l_Lean_privateToUserName(v_declName_3801_);
v___x_3845_ = lean_box(0);
v___x_3846_ = l_Lean_Name_replacePrefix(v___x_3844_, v___x_3836_, v___x_3845_);
v___x_3847_ = l_Lean_Name_replacePrefix(v___x_3846_, v___x_3843_, v___x_3845_);
lean_inc_ref(v_e_3768_);
v___f_3848_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed), 13, 2);
lean_closure_set(v___f_3848_, 0, v___x_3847_);
lean_closure_set(v___f_3848_, 1, v_e_3768_);
v___x_3849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6));
v___x_3851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9);
v___x_3852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3838_, v_options_3837_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3929_; uint8_t v___x_3930_; 
v___x_3929_ = l_Lean_trace_profiler;
v___x_3930_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3837_, v___x_3929_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; 
lean_dec_ref(v___f_3848_);
lean_inc_ref(v_e_3768_);
v___x_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3841_, v_e_3768_, v_snd_3793_, v_proc_3797_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v_snd_3793_);
v___y_3813_ = v___x_3931_;
goto v___jp_3812_;
}
else
{
goto v___jp_3880_;
}
}
else
{
goto v___jp_3880_;
}
v___jp_3853_:
{
lean_object* v___x_3857_; double v___x_3858_; double v___x_3859_; double v___x_3860_; double v___x_3861_; double v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3857_ = lean_io_mono_nanos_now();
v___x_3858_ = lean_float_of_nat(v___y_3855_);
v___x_3859_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10);
v___x_3860_ = lean_float_div(v___x_3858_, v___x_3859_);
v___x_3861_ = lean_float_of_nat(v___x_3857_);
v___x_3862_ = lean_float_div(v___x_3861_, v___x_3859_);
v___x_3863_ = lean_box_float(v___x_3860_);
v___x_3864_ = lean_box_float(v___x_3862_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v_a_3856_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3849_, v_hasTrace_3839_, v___x_3850_, v_options_3837_, v___x_3852_, v___y_3854_, v___f_3848_, v___x_3866_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
v___y_3813_ = v___x_3867_;
goto v___jp_3812_;
}
v___jp_3868_:
{
lean_object* v___x_3872_; double v___x_3873_; double v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3872_ = lean_io_get_num_heartbeats();
v___x_3873_ = lean_float_of_nat(v___y_3869_);
v___x_3874_ = lean_float_of_nat(v___x_3872_);
v___x_3875_ = lean_box_float(v___x_3873_);
v___x_3876_ = lean_box_float(v___x_3874_);
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3875_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v_a_3871_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3849_, v_hasTrace_3839_, v___x_3850_, v_options_3837_, v___x_3852_, v___y_3870_, v___f_3848_, v___x_3878_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
v___y_3813_ = v___x_3879_;
goto v___jp_3812_;
}
v___jp_3880_:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3781_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3884_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3837_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_io_mono_nanos_now();
lean_inc_ref(v_e_3768_);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3841_, v_e_3768_, v_snd_3793_, v_proc_3797_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v_snd_3793_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set_tag(v___x_3889_, 1);
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
v___y_3854_ = v_a_3882_;
v___y_3855_ = v___x_3885_;
v_a_3856_ = v___x_3892_;
goto v___jp_3853_;
}
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
v_a_3895_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3886_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3886_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
lean_ctor_set_tag(v___x_3897_, 0);
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
v___y_3854_ = v_a_3882_;
v___y_3855_ = v___x_3885_;
v_a_3856_ = v___x_3900_;
goto v___jp_3853_;
}
}
}
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_e_3768_);
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3841_, v_e_3768_, v_snd_3793_, v_proc_3797_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v_snd_3793_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 1);
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
v___y_3869_ = v___x_3903_;
v___y_3870_ = v_a_3882_;
v_a_3871_ = v___x_3910_;
goto v___jp_3868_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_a_3913_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3904_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3904_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
lean_ctor_set_tag(v___x_3915_, 0);
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v___y_3869_ = v___x_3903_;
v___y_3870_ = v_a_3882_;
v_a_3871_ = v___x_3918_;
goto v___jp_3868_;
}
}
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v___f_3848_);
lean_del_object(v___x_3799_);
lean_dec_ref(v_proc_3797_);
lean_del_object(v___x_3795_);
lean_dec(v_snd_3793_);
lean_dec_ref(v_e_3768_);
v_a_3921_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3881_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3881_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_3801_);
lean_del_object(v___x_3799_);
lean_dec_ref(v_proc_3797_);
lean_del_object(v___x_3795_);
lean_dec(v_snd_3793_);
v_a_3784_ = v___x_3810_;
goto v___jp_3783_;
}
v___jp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___y_3804_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 1, v___x_3802_);
lean_ctor_set(v___x_3795_, 0, v___x_3805_);
v___x_3807_ = v___x_3795_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3802_);
v___x_3807_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
return v___x_3808_;
}
}
v___jp_3812_:
{
if (lean_obj_tag(v___y_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3827_; 
v_a_3814_ = lean_ctor_get(v___y_3813_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___y_3813_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3816_ = v___y_3813_;
v_isShared_3817_ = v_isSharedCheck_3827_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___y_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3827_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
if (lean_obj_tag(v_a_3814_) == 1)
{
lean_del_object(v___x_3816_);
lean_del_object(v___x_3799_);
lean_dec_ref(v_e_3768_);
v___y_3804_ = v_a_3814_;
goto v___jp_3803_;
}
else
{
if (v___x_3811_ == 0)
{
lean_del_object(v___x_3795_);
if (lean_obj_tag(v_a_3814_) == 0)
{
uint8_t v_done_3818_; 
v_done_3818_ = lean_ctor_get_uint8(v_a_3814_, 0);
if (v_done_3818_ == 1)
{
uint8_t v_contextDependent_3819_; 
v_contextDependent_3819_ = lean_ctor_get_uint8(v_a_3814_, 1);
if (v_contextDependent_3819_ == 0)
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
lean_dec_ref(v_e_3768_);
v___x_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3814_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 1, v___x_3802_);
lean_ctor_set(v___x_3799_, 0, v___x_3820_);
v___x_3822_ = v___x_3799_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3802_);
v___x_3822_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3824_; 
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3822_);
v___x_3824_ = v___x_3816_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
else
{
lean_dec_ref_known(v_a_3814_, 0);
lean_del_object(v___x_3816_);
lean_del_object(v___x_3799_);
v_a_3784_ = v___x_3810_;
goto v___jp_3783_;
}
}
else
{
lean_dec_ref_known(v_a_3814_, 0);
lean_del_object(v___x_3816_);
lean_del_object(v___x_3799_);
v_a_3784_ = v___x_3810_;
goto v___jp_3783_;
}
}
else
{
lean_del_object(v___x_3816_);
lean_dec(v_a_3814_);
lean_del_object(v___x_3799_);
v_a_3784_ = v___x_3810_;
goto v___jp_3783_;
}
}
else
{
lean_del_object(v___x_3816_);
lean_del_object(v___x_3799_);
lean_dec_ref(v_e_3768_);
v___y_3804_ = v_a_3814_;
goto v___jp_3803_;
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3799_);
lean_del_object(v___x_3795_);
lean_dec_ref(v_e_3768_);
v_a_3828_ = lean_ctor_get(v___y_3813_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___y_3813_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___y_3813_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___y_3813_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
}
}
v___jp_3783_:
{
size_t v___x_3785_; size_t v___x_3786_; 
v___x_3785_ = ((size_t)1ULL);
v___x_3786_ = lean_usize_add(v_i_3771_, v___x_3785_);
lean_inc_ref(v_a_3784_);
v_i_3771_ = v___x_3786_;
v_b_3772_ = v_a_3784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object* v_erased_3936_, lean_object* v_e_3937_, lean_object* v_as_3938_, lean_object* v_sz_3939_, lean_object* v_i_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
size_t v_sz_boxed_3952_; size_t v_i_boxed_3953_; lean_object* v_res_3954_; 
v_sz_boxed_3952_ = lean_unbox_usize(v_sz_3939_);
lean_dec(v_sz_3939_);
v_i_boxed_3953_ = lean_unbox_usize(v_i_3940_);
lean_dec(v_i_3940_);
v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3936_, v_e_3937_, v_as_3938_, v_sz_boxed_3952_, v_i_boxed_3953_, v_b_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v_as_3938_);
lean_dec_ref(v_erased_3936_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object* v_tree_3957_, lean_object* v_erased_3958_, lean_object* v_e_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v_candidates_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_candidates_3970_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_tree_3957_, v_e_3959_);
v___x_3971_ = lean_array_get_size(v_candidates_3970_);
v___x_3972_ = lean_unsigned_to_nat(0u);
v___x_3973_ = lean_nat_dec_eq(v___x_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; size_t v_sz_3975_; size_t v___x_3976_; lean_object* v___x_3977_; 
v___x_3974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v_sz_3975_ = lean_array_size(v_candidates_3970_);
v___x_3976_ = ((size_t)0ULL);
v___x_3977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3958_, v_e_3959_, v_candidates_3970_, v_sz_3975_, v___x_3976_, v___x_3974_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
lean_dec_ref(v_candidates_3970_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3991_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_3991_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3991_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v_fst_3982_; 
v_fst_3982_ = lean_ctor_get(v_a_3978_, 0);
lean_inc(v_fst_3982_);
lean_dec(v_a_3978_);
if (lean_obj_tag(v_fst_3982_) == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3983_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3983_, 0, v___x_3973_);
lean_ctor_set_uint8(v___x_3983_, 1, v___x_3973_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_3983_);
v___x_3985_ = v___x_3980_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
else
{
lean_object* v_val_3987_; lean_object* v___x_3989_; 
v_val_3987_ = lean_ctor_get(v_fst_3982_, 0);
lean_inc(v_val_3987_);
lean_dec_ref_known(v_fst_3982_, 1);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v_val_3987_);
v___x_3989_ = v___x_3980_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_val_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
v_a_3992_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3977_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3977_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref(v_candidates_3970_);
lean_dec_ref(v_e_3959_);
v___x_4000_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0));
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
return v___x_4001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object* v_tree_4002_, lean_object* v_erased_4003_, lean_object* v_e_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_4002_, v_erased_4003_, v_e_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_erased_4003_);
lean_dec_ref(v_tree_4002_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object* v_00_u03b1_4016_, lean_object* v_x_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_4017_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4029_, lean_object* v_x_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(v_00_u03b1_4029_, v_x_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object* v_oldTraces_4042_, lean_object* v_data_4043_, lean_object* v_ref_4044_, lean_object* v_msg_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_4042_, v_data_4043_, v_ref_4044_, v_msg_4045_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object* v_oldTraces_4057_, lean_object* v_data_4058_, lean_object* v_ref_4059_, lean_object* v_msg_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_oldTraces_4057_, v_data_4058_, v_ref_4059_, v_msg_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
return v_res_4071_;
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
