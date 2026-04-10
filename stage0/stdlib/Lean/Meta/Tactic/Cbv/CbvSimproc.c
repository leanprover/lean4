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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_initializing();
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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(lean_object* v_msg_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0);
v___x_251_ = lean_panic_fn_borrowed(v___x_250_, v_msg_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_ks_256_; lean_object* v_vs_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_281_; 
v_ks_256_ = lean_ctor_get(v_x_252_, 0);
v_vs_257_ = lean_ctor_get(v_x_252_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_281_ == 0)
{
v___x_259_ = v_x_252_;
v_isShared_260_ = v_isSharedCheck_281_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_vs_257_);
lean_inc(v_ks_256_);
lean_dec(v_x_252_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_281_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_array_get_size(v_ks_256_);
v___x_262_ = lean_nat_dec_lt(v_x_253_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v_x_253_);
v___x_263_ = lean_array_push(v_ks_256_, v_x_254_);
v___x_264_ = lean_array_push(v_vs_257_, v_x_255_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_264_);
lean_ctor_set(v___x_259_, 0, v___x_263_);
v___x_266_ = v___x_259_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v_k_x27_268_; uint8_t v___x_269_; 
v_k_x27_268_ = lean_array_fget_borrowed(v_ks_256_, v_x_253_);
v___x_269_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_254_, v_k_x27_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_271_; 
if (v_isShared_260_ == 0)
{
v___x_271_ = v___x_259_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_ks_256_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_vs_257_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_x_253_, v___x_272_);
lean_dec(v_x_253_);
v_x_252_ = v___x_271_;
v_x_253_ = v___x_273_;
goto _start;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_array_fset(v_ks_256_, v_x_253_, v_x_254_);
v___x_277_ = lean_array_fset(v_vs_257_, v_x_253_, v_x_255_);
lean_dec(v_x_253_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_277_);
lean_ctor_set(v___x_259_, 0, v___x_276_);
v___x_279_ = v___x_259_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(lean_object* v_n_282_, lean_object* v_k_283_, lean_object* v_v_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(v_n_282_, v___x_285_, v_k_283_, v_v_284_);
return v___x_286_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0(void){
_start:
{
size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; 
v___x_287_ = ((size_t)5ULL);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_shift_left(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; 
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0);
v___x_292_ = lean_usize_sub(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(lean_object* v_x_294_, size_t v_x_295_, size_t v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v_es_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v_j_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_es_299_ = lean_ctor_get(v_x_294_, 0);
v___x_300_ = ((size_t)5ULL);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_303_ = lean_usize_land(v_x_295_, v___x_302_);
v_j_304_ = lean_usize_to_nat(v___x_303_);
v___x_305_ = lean_array_get_size(v_es_299_);
v___x_306_ = lean_nat_dec_lt(v_j_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_j_304_);
lean_dec(v_x_298_);
lean_dec(v_x_297_);
return v_x_294_;
}
else
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_343_; 
lean_inc_ref(v_es_299_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_x_294_, 0);
lean_dec(v_unused_344_);
v___x_308_ = v_x_294_;
v_isShared_309_ = v_isSharedCheck_343_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_x_294_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_343_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_v_310_; lean_object* v___x_311_; lean_object* v_xs_x27_312_; lean_object* v___y_314_; 
v_v_310_ = lean_array_fget(v_es_299_, v_j_304_);
v___x_311_ = lean_box(0);
v_xs_x27_312_ = lean_array_fset(v_es_299_, v_j_304_, v___x_311_);
switch(lean_obj_tag(v_v_310_))
{
case 0:
{
lean_object* v_key_319_; lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v_key_319_ = lean_ctor_get(v_v_310_, 0);
v_val_320_ = lean_ctor_get(v_v_310_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_v_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_322_ = v_v_310_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_inc(v_key_319_);
lean_dec(v_v_310_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_297_, v_key_319_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_del_object(v___x_322_);
v___x_325_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_319_, v_val_320_, v_x_297_, v_x_298_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
else
{
lean_object* v___x_328_; 
lean_dec(v_val_320_);
lean_dec(v_key_319_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v_x_298_);
lean_ctor_set(v___x_322_, 0, v_x_297_);
v___x_328_ = v___x_322_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_x_297_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_x_298_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v___y_314_ = v___x_328_;
goto v___jp_313_;
}
}
}
}
case 1:
{
lean_object* v_node_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_341_; 
v_node_331_ = lean_ctor_get(v_v_310_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_v_310_);
if (v_isSharedCheck_341_ == 0)
{
v___x_333_ = v_v_310_;
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_node_331_);
lean_dec(v_v_310_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_335_ = lean_usize_shift_right(v_x_295_, v___x_300_);
v___x_336_ = lean_usize_add(v_x_296_, v___x_301_);
v___x_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_node_331_, v___x_335_, v___x_336_, v_x_297_, v_x_298_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_337_);
v___x_339_ = v___x_333_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v___y_314_ = v___x_339_;
goto v___jp_313_;
}
}
}
default: 
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_x_297_);
lean_ctor_set(v___x_342_, 1, v_x_298_);
v___y_314_ = v___x_342_;
goto v___jp_313_;
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_array_fset(v_xs_x27_312_, v_j_304_, v___y_314_);
lean_dec(v_j_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_315_);
v___x_317_ = v___x_308_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_ks_345_; lean_object* v_vs_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_366_; 
v_ks_345_ = lean_ctor_get(v_x_294_, 0);
v_vs_346_ = lean_ctor_get(v_x_294_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_366_ == 0)
{
v___x_348_ = v_x_294_;
v_isShared_349_ = v_isSharedCheck_366_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_vs_346_);
lean_inc(v_ks_345_);
lean_dec(v_x_294_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_366_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_ks_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_vs_346_);
v___x_351_ = v_reuseFailAlloc_365_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v_newNode_352_; uint8_t v___y_354_; size_t v___x_360_; uint8_t v___x_361_; 
v_newNode_352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(v___x_351_, v_x_297_, v_x_298_);
v___x_360_ = ((size_t)7ULL);
v___x_361_ = lean_usize_dec_le(v___x_360_, v_x_296_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_352_);
v___x_363_ = lean_unsigned_to_nat(4u);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
lean_dec(v___x_362_);
v___y_354_ = v___x_364_;
goto v___jp_353_;
}
else
{
v___y_354_ = v___x_361_;
goto v___jp_353_;
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
lean_object* v_ks_355_; lean_object* v_vs_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_ks_355_ = lean_ctor_get(v_newNode_352_, 0);
lean_inc_ref(v_ks_355_);
v_vs_356_ = lean_ctor_get(v_newNode_352_, 1);
lean_inc_ref(v_vs_356_);
lean_dec_ref(v_newNode_352_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2);
v___x_359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_x_296_, v_ks_355_, v_vs_356_, v___x_357_, v___x_358_);
lean_dec_ref(v_vs_356_);
lean_dec_ref(v_ks_355_);
return v___x_359_;
}
else
{
return v_newNode_352_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(size_t v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_array_get_size(v_keys_368_);
v___x_373_ = lean_nat_dec_lt(v_i_370_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec(v_i_370_);
return v_entries_371_;
}
else
{
lean_object* v_k_374_; lean_object* v_v_375_; uint64_t v___x_376_; size_t v_h_377_; size_t v___x_378_; lean_object* v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v_h_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_k_374_ = lean_array_fget_borrowed(v_keys_368_, v_i_370_);
v_v_375_ = lean_array_fget_borrowed(v_vals_369_, v_i_370_);
v___x_376_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_374_);
v_h_377_ = lean_uint64_to_usize(v___x_376_);
v___x_378_ = ((size_t)5ULL);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v_depth_367_, v___x_380_);
v___x_382_ = lean_usize_mul(v___x_378_, v___x_381_);
v_h_383_ = lean_usize_shift_right(v_h_377_, v___x_382_);
v___x_384_ = lean_nat_add(v_i_370_, v___x_379_);
lean_dec(v_i_370_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_entries_371_, v_h_383_, v_depth_367_, v_k_374_, v_v_375_);
v_i_370_ = v___x_384_;
v_entries_371_ = v___x_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
size_t v_depth_boxed_392_; lean_object* v_res_393_; 
v_depth_boxed_392_ = lean_unbox_usize(v_depth_387_);
lean_dec(v_depth_387_);
v_res_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_depth_boxed_392_, v_keys_388_, v_vals_389_, v_i_390_, v_entries_391_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_2100__boxed_399_; size_t v_x_2101__boxed_400_; lean_object* v_res_401_; 
v_x_2100__boxed_399_ = lean_unbox_usize(v_x_395_);
lean_dec(v_x_395_);
v_x_2101__boxed_400_ = lean_unbox_usize(v_x_396_);
lean_dec(v_x_396_);
v_res_401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_394_, v_x_2100__boxed_399_, v_x_2101__boxed_400_, v_x_397_, v_x_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_403_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_402_, v___x_406_, v___x_407_, v_x_403_, v_x_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(lean_object* v_x_409_, lean_object* v_keys_410_, lean_object* v_v_411_, lean_object* v_k_412_, lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_c_416_; lean_object* v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_x_409_, v___x_414_);
v_c_416_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_410_, v_v_411_, v___x_415_);
lean_dec(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_k_412_);
lean_ctor_set(v___x_417_, 1, v_c_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0___boxed(lean_object* v_x_418_, lean_object* v_keys_419_, lean_object* v_v_420_, lean_object* v_k_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_418_, v_keys_419_, v_v_420_, v_k_421_, v_x_422_);
lean_dec_ref(v_keys_419_);
lean_dec(v_x_418_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(lean_object* v_a_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_fst_426_; lean_object* v_fst_427_; uint8_t v___x_428_; 
v_fst_426_ = lean_ctor_get(v_a_424_, 0);
v_fst_427_ = lean_ctor_get(v_b_425_, 0);
v___x_428_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_426_, v_fst_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1___boxed(lean_object* v_a_429_, lean_object* v_b_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_a_429_, v_b_430_);
lean_dec_ref(v_b_430_);
lean_dec_ref(v_a_429_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(lean_object* v_vs_433_, lean_object* v_v_434_, lean_object* v_i_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_array_get_size(v_vs_433_);
v___x_437_ = lean_nat_dec_lt(v_i_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_dec(v_i_435_);
v___x_438_ = lean_array_push(v_vs_433_, v_v_434_);
return v___x_438_;
}
else
{
lean_object* v_toCbvSimprocOLeanEntry_439_; lean_object* v_declName_440_; lean_object* v___x_441_; lean_object* v_toCbvSimprocOLeanEntry_442_; lean_object* v_declName_443_; uint8_t v___x_444_; 
v_toCbvSimprocOLeanEntry_439_ = lean_ctor_get(v_v_434_, 0);
v_declName_440_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_439_, 0);
v___x_441_ = lean_array_fget_borrowed(v_vs_433_, v_i_435_);
v_toCbvSimprocOLeanEntry_442_ = lean_ctor_get(v___x_441_, 0);
v_declName_443_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_442_, 0);
v___x_444_ = lean_name_eq(v_declName_440_, v_declName_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_i_435_, v___x_445_);
lean_dec(v_i_435_);
v_i_435_ = v___x_446_;
goto _start;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_array_fset(v_vs_433_, v_i_435_, v_v_434_);
lean_dec(v_i_435_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(lean_object* v_vs_449_, lean_object* v_v_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(v_vs_449_, v_v_450_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(lean_object* v_x_457_, lean_object* v_keys_458_, lean_object* v_v_459_, lean_object* v_k_460_, lean_object* v_as_461_, lean_object* v_k_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_mid_467_; lean_object* v_midVal_468_; uint8_t v___x_469_; 
v___x_465_ = lean_nat_add(v_x_463_, v_x_464_);
v___x_466_ = lean_unsigned_to_nat(1u);
v_mid_467_ = lean_nat_shiftr(v___x_465_, v___x_466_);
lean_dec(v___x_465_);
v_midVal_468_ = lean_array_fget(v_as_461_, v_mid_467_);
v___x_469_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_midVal_468_, v_k_462_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; 
lean_dec(v_x_464_);
v___x_470_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_462_, v_midVal_468_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
lean_dec(v_x_463_);
v___x_471_ = lean_array_get_size(v_as_461_);
v___x_472_ = lean_nat_dec_lt(v_mid_467_, v___x_471_);
if (v___x_472_ == 0)
{
lean_dec(v_midVal_468_);
lean_dec(v_mid_467_);
lean_dec(v_k_460_);
lean_dec_ref(v_v_459_);
return v_as_461_;
}
else
{
lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_snd_473_ = lean_ctor_get(v_midVal_468_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_midVal_468_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_midVal_468_, 0);
lean_dec(v_unused_486_);
v___x_475_ = v_midVal_468_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_dec(v_midVal_468_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v_xs_x27_478_; lean_object* v___x_479_; lean_object* v_c_480_; lean_object* v___x_482_; 
v___x_477_ = lean_box(0);
v_xs_x27_478_ = lean_array_fset(v_as_461_, v_mid_467_, v___x_477_);
v___x_479_ = lean_nat_add(v_x_457_, v___x_466_);
v_c_480_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_458_, v_v_459_, v___x_479_, v_snd_473_);
lean_dec(v___x_479_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_c_480_);
lean_ctor_set(v___x_475_, 0, v_k_460_);
v___x_482_ = v___x_475_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_c_480_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_array_fset(v_xs_x27_478_, v_mid_467_, v___x_482_);
lean_dec(v_mid_467_);
return v___x_483_;
}
}
}
}
else
{
lean_dec(v_midVal_468_);
v_x_464_ = v_mid_467_;
goto _start;
}
}
else
{
uint8_t v___x_488_; 
lean_dec(v_midVal_468_);
v___x_488_ = lean_nat_dec_eq(v_mid_467_, v_x_463_);
if (v___x_488_ == 0)
{
lean_dec(v_x_463_);
v_x_463_ = v_mid_467_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v_c_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_j_494_; lean_object* v_as_495_; lean_object* v___x_496_; 
lean_dec(v_mid_467_);
lean_dec(v_x_464_);
v___x_490_ = lean_nat_add(v_x_457_, v___x_466_);
v_c_491_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_458_, v_v_459_, v___x_490_);
lean_dec(v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_k_460_);
lean_ctor_set(v___x_492_, 1, v_c_491_);
v___x_493_ = lean_nat_add(v_x_463_, v___x_466_);
lean_dec(v_x_463_);
v_j_494_ = lean_array_get_size(v_as_461_);
v_as_495_ = lean_array_push(v_as_461_, v___x_492_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_493_, v_as_495_, v_j_494_);
lean_dec(v___x_493_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(lean_object* v_x_497_, lean_object* v_keys_498_, lean_object* v_v_499_, lean_object* v_k_500_, lean_object* v_as_501_, lean_object* v_k_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_array_get_size(v_as_501_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_array_fget_borrowed(v_as_501_, v___x_504_);
v___x_507_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_502_, v___x_506_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v___x_506_, v_k_502_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_lt(v___x_504_, v___x_503_);
if (v___x_509_ == 0)
{
lean_dec(v_k_500_);
lean_dec_ref(v_v_499_);
return v_as_501_;
}
else
{
lean_object* v___x_510_; lean_object* v_xs_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc(v___x_506_);
v___x_510_ = lean_box(0);
v_xs_x27_511_ = lean_array_fset(v_as_501_, v___x_504_, v___x_510_);
v___x_512_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_506_);
v___x_513_ = lean_array_fset(v_xs_x27_511_, v___x_504_, v___x_512_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_sub(v___x_503_, v___x_514_);
v___x_516_ = lean_array_fget_borrowed(v_as_501_, v___x_515_);
v___x_517_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v___x_516_, v_k_502_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_502_, v___x_516_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_lt(v___x_515_, v___x_503_);
if (v___x_519_ == 0)
{
lean_dec(v___x_515_);
lean_dec(v_k_500_);
lean_dec_ref(v_v_499_);
return v_as_501_;
}
else
{
lean_object* v___x_520_; lean_object* v_xs_x27_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc(v___x_516_);
v___x_520_ = lean_box(0);
v_xs_x27_521_ = lean_array_fset(v_as_501_, v___x_515_, v___x_520_);
v___x_522_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_516_);
v___x_523_ = lean_array_fset(v_xs_x27_521_, v___x_515_, v___x_522_);
lean_dec(v___x_515_);
return v___x_523_;
}
}
else
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v_as_501_, v_k_502_, v___x_504_, v___x_515_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_515_);
v___x_525_ = lean_box(0);
v___x_526_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_525_);
v___x_527_ = lean_array_push(v_as_501_, v___x_526_);
return v___x_527_;
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_as_530_; lean_object* v___x_531_; 
v___x_528_ = lean_box(0);
v___x_529_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_528_);
v_as_530_ = lean_array_push(v_as_501_, v___x_529_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_504_, v_as_530_, v___x_503_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_box(0);
v___x_533_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_532_);
v___x_534_ = lean_array_push(v_as_501_, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object* v_keys_535_, lean_object* v_v_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_vs_539_; lean_object* v_children_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_557_; 
v_vs_539_ = lean_ctor_get(v_x_538_, 0);
v_children_540_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_542_ = v_x_538_;
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_children_540_);
lean_inc(v_vs_539_);
lean_dec(v_x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_array_get_size(v_keys_535_);
v___x_545_ = lean_nat_dec_lt(v_x_537_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(v_vs_539_, v_v_536_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_546_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_children_540_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v_k_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_c_553_; lean_object* v___x_555_; 
v_k_550_ = lean_array_fget_borrowed(v_keys_535_, v_x_537_);
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1));
lean_inc_n(v_k_550_, 2);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_k_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v_c_553_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(v_x_537_, v_keys_535_, v_v_536_, v_k_550_, v_children_540_, v___x_552_);
lean_dec_ref(v___x_552_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_c_553_);
v___x_555_ = v___x_542_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_vs_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_c_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(lean_object* v_x_558_, lean_object* v_keys_559_, lean_object* v_v_560_, lean_object* v_k_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_snd_563_ = lean_ctor_get(v_x_562_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_x_562_, 0);
lean_dec(v_unused_574_);
v___x_565_ = v_x_562_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_dec(v_x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_c_569_; lean_object* v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_x_558_, v___x_567_);
v_c_569_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_559_, v_v_560_, v___x_568_, v_snd_563_);
lean_dec(v___x_568_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_c_569_);
lean_ctor_set(v___x_565_, 0, v_k_561_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_k_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_c_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2___boxed(lean_object* v_x_575_, lean_object* v_keys_576_, lean_object* v_v_577_, lean_object* v_k_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_575_, v_keys_576_, v_v_577_, v_k_578_, v_x_579_);
lean_dec_ref(v_keys_576_);
lean_dec(v_x_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___boxed(lean_object* v_keys_581_, lean_object* v_v_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_581_, v_v_582_, v_x_583_, v_x_584_);
lean_dec(v_x_583_);
lean_dec_ref(v_keys_581_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg___boxed(lean_object* v_x_586_, lean_object* v_keys_587_, lean_object* v_v_588_, lean_object* v_k_589_, lean_object* v_as_590_, lean_object* v_k_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_586_, v_keys_587_, v_v_588_, v_k_589_, v_as_590_, v_k_591_, v_x_592_, v_x_593_);
lean_dec_ref(v_k_591_);
lean_dec_ref(v_keys_587_);
lean_dec(v_x_586_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___boxed(lean_object* v_x_595_, lean_object* v_keys_596_, lean_object* v_v_597_, lean_object* v_k_598_, lean_object* v_as_599_, lean_object* v_k_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(v_x_595_, v_keys_596_, v_v_597_, v_k_598_, v_as_599_, v_k_600_);
lean_dec_ref(v_k_600_);
lean_dec_ref(v_keys_596_);
lean_dec(v_x_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_i_604_, lean_object* v_k_605_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_array_get_size(v_keys_602_);
v___x_607_ = lean_nat_dec_lt(v_i_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec(v_i_604_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
else
{
lean_object* v_k_x27_609_; uint8_t v___x_610_; 
v_k_x27_609_ = lean_array_fget_borrowed(v_keys_602_, v_i_604_);
v___x_610_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_605_, v_k_x27_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_i_604_, v___x_611_);
lean_dec(v_i_604_);
v_i_604_ = v___x_612_;
goto _start;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_array_fget_borrowed(v_vals_603_, v_i_604_);
lean_dec(v_i_604_);
lean_inc(v___x_614_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_keys_616_, lean_object* v_vals_617_, lean_object* v_i_618_, lean_object* v_k_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_keys_616_, v_vals_617_, v_i_618_, v_k_619_);
lean_dec(v_k_619_);
lean_dec_ref(v_vals_617_);
lean_dec_ref(v_keys_616_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(lean_object* v_x_621_, size_t v_x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v_es_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_645_; 
v_es_624_ = lean_ctor_get(v_x_621_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_645_ == 0)
{
v___x_626_ = v_x_621_;
v_isShared_627_ = v_isSharedCheck_645_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_es_624_);
lean_dec(v_x_621_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_645_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v_j_632_; lean_object* v___x_633_; 
v___x_628_ = lean_box(2);
v___x_629_ = ((size_t)5ULL);
v___x_630_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_631_ = lean_usize_land(v_x_622_, v___x_630_);
v_j_632_ = lean_usize_to_nat(v___x_631_);
v___x_633_ = lean_array_get(v___x_628_, v_es_624_, v_j_632_);
lean_dec(v_j_632_);
lean_dec_ref(v_es_624_);
switch(lean_obj_tag(v___x_633_))
{
case 0:
{
lean_object* v_key_634_; lean_object* v_val_635_; uint8_t v___x_636_; 
v_key_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_key_634_);
v_val_635_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_val_635_);
lean_dec_ref(v___x_633_);
v___x_636_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_623_, v_key_634_);
lean_dec(v_key_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v_val_635_);
lean_del_object(v___x_626_);
v___x_637_ = lean_box(0);
return v___x_637_;
}
else
{
lean_object* v___x_639_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
lean_ctor_set(v___x_626_, 0, v_val_635_);
v___x_639_ = v___x_626_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_val_635_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
case 1:
{
lean_object* v_node_641_; size_t v___x_642_; 
lean_del_object(v___x_626_);
v_node_641_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_node_641_);
lean_dec_ref(v___x_633_);
v___x_642_ = lean_usize_shift_right(v_x_622_, v___x_629_);
v_x_621_ = v_node_641_;
v_x_622_ = v___x_642_;
goto _start;
}
default: 
{
lean_object* v___x_644_; 
lean_del_object(v___x_626_);
v___x_644_ = lean_box(0);
return v___x_644_;
}
}
}
}
else
{
lean_object* v_ks_646_; lean_object* v_vs_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_ks_646_ = lean_ctor_get(v_x_621_, 0);
lean_inc_ref(v_ks_646_);
v_vs_647_ = lean_ctor_get(v_x_621_, 1);
lean_inc_ref(v_vs_647_);
lean_dec_ref(v_x_621_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_ks_646_, v_vs_647_, v___x_648_, v_x_623_);
lean_dec_ref(v_vs_647_);
lean_dec_ref(v_ks_646_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
size_t v_x_2540__boxed_653_; lean_object* v_res_654_; 
v_x_2540__boxed_653_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_res_654_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_650_, v_x_2540__boxed_653_, v_x_652_);
lean_dec(v_x_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint64_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_656_);
v___x_658_ = lean_uint64_to_usize(v___x_657_);
v___x_659_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_655_, v___x_658_, v_x_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_x_660_, v_x_661_);
lean_dec(v_x_661_);
return v_res_662_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_666_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2));
v___x_667_ = lean_unsigned_to_nat(23u);
v___x_668_ = lean_unsigned_to_nat(166u);
v___x_669_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1));
v___x_670_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0));
v___x_671_ = l_mkPanicMessageWithDecl(v___x_670_, v___x_669_, v___x_668_, v___x_667_, v___x_666_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object* v_d_672_, lean_object* v_keys_673_, lean_object* v_v_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_array_get_size(v_keys_673_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_nat_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_k_679_; lean_object* v___x_680_; 
v___x_678_ = lean_box(0);
v_k_679_ = lean_array_get_borrowed(v___x_678_, v_keys_673_, v___x_676_);
lean_inc_ref(v_d_672_);
v___x_680_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_d_672_, v_k_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v_c_682_; lean_object* v___x_683_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v_c_682_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_673_, v_v_674_, v___x_681_);
lean_inc(v_k_679_);
v___x_683_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_d_672_, v_k_679_, v_c_682_);
return v___x_683_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_685_; lean_object* v_c_686_; lean_object* v___x_687_; 
v_val_684_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___x_680_);
v___x_685_ = lean_unsigned_to_nat(1u);
v_c_686_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_673_, v_v_674_, v___x_685_, v_val_684_);
lean_inc(v_k_679_);
v___x_687_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_d_672_, v_k_679_, v_c_686_);
return v___x_687_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref(v_v_674_);
lean_dec_ref(v_d_672_);
v___x_688_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
v___x_689_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object* v_d_690_, lean_object* v_keys_691_, lean_object* v_v_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_690_, v_keys_691_, v_v_692_);
lean_dec_ref(v_keys_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_ks_698_; lean_object* v_vs_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_723_; 
v_ks_698_ = lean_ctor_get(v_x_694_, 0);
v_vs_699_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_723_ == 0)
{
v___x_701_ = v_x_694_;
v_isShared_702_ = v_isSharedCheck_723_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_vs_699_);
lean_inc(v_ks_698_);
lean_dec(v_x_694_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_723_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_array_get_size(v_ks_698_);
v___x_704_ = lean_nat_dec_lt(v_x_695_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
lean_dec(v_x_695_);
v___x_705_ = lean_array_push(v_ks_698_, v_x_696_);
v___x_706_ = lean_array_push(v_vs_699_, v_x_697_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_706_);
lean_ctor_set(v___x_701_, 0, v___x_705_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_k_x27_710_; uint8_t v___x_711_; 
v_k_x27_710_ = lean_array_fget_borrowed(v_ks_698_, v_x_695_);
v___x_711_ = lean_name_eq(v_x_696_, v_k_x27_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; 
if (v_isShared_702_ == 0)
{
v___x_713_ = v___x_701_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_ks_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_vs_699_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_add(v_x_695_, v___x_714_);
lean_dec(v_x_695_);
v_x_694_ = v___x_713_;
v_x_695_ = v___x_715_;
goto _start;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_array_fset(v_ks_698_, v_x_695_, v_x_696_);
v___x_719_ = lean_array_fset(v_vs_699_, v_x_695_, v_x_697_);
lean_dec(v_x_695_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_719_);
lean_ctor_set(v___x_701_, 0, v___x_718_);
v___x_721_ = v___x_701_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_724_, lean_object* v_k_725_, lean_object* v_v_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_724_, v___x_727_, v_k_725_, v_v_726_);
return v___x_728_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_729_; uint64_t v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1723u);
v___x_730_ = lean_uint64_of_nat(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_732_, size_t v_x_733_, size_t v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
lean_object* v_es_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v_j_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_es_737_ = lean_ctor_get(v_x_732_, 0);
v___x_738_ = ((size_t)5ULL);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_741_ = lean_usize_land(v_x_733_, v___x_740_);
v_j_742_ = lean_usize_to_nat(v___x_741_);
v___x_743_ = lean_array_get_size(v_es_737_);
v___x_744_ = lean_nat_dec_lt(v_j_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_j_742_);
lean_dec(v_x_736_);
lean_dec(v_x_735_);
return v_x_732_;
}
else
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_781_; 
lean_inc_ref(v_es_737_);
v_isSharedCheck_781_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_x_732_, 0);
lean_dec(v_unused_782_);
v___x_746_ = v_x_732_;
v_isShared_747_ = v_isSharedCheck_781_;
goto v_resetjp_745_;
}
else
{
lean_dec(v_x_732_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_781_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_v_748_; lean_object* v___x_749_; lean_object* v_xs_x27_750_; lean_object* v___y_752_; 
v_v_748_ = lean_array_fget(v_es_737_, v_j_742_);
v___x_749_ = lean_box(0);
v_xs_x27_750_ = lean_array_fset(v_es_737_, v_j_742_, v___x_749_);
switch(lean_obj_tag(v_v_748_))
{
case 0:
{
lean_object* v_key_757_; lean_object* v_val_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
v_key_757_ = lean_ctor_get(v_v_748_, 0);
v_val_758_ = lean_ctor_get(v_v_748_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_768_ == 0)
{
v___x_760_ = v_v_748_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_val_758_);
lean_inc(v_key_757_);
lean_dec(v_v_748_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; 
v___x_762_ = lean_name_eq(v_x_735_, v_key_757_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_del_object(v___x_760_);
v___x_763_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_757_, v_val_758_, v_x_735_, v_x_736_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
v___y_752_ = v___x_764_;
goto v___jp_751_;
}
else
{
lean_object* v___x_766_; 
lean_dec(v_val_758_);
lean_dec(v_key_757_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_x_736_);
lean_ctor_set(v___x_760_, 0, v_x_735_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_x_735_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_x_736_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v___y_752_ = v___x_766_;
goto v___jp_751_;
}
}
}
}
case 1:
{
lean_object* v_node_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_779_; 
v_node_769_ = lean_ctor_get(v_v_748_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_779_ == 0)
{
v___x_771_ = v_v_748_;
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_node_769_);
lean_dec(v_v_748_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_773_ = lean_usize_shift_right(v_x_733_, v___x_738_);
v___x_774_ = lean_usize_add(v_x_734_, v___x_739_);
v___x_775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_769_, v___x_773_, v___x_774_, v_x_735_, v_x_736_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_777_ = v___x_771_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v___y_752_ = v___x_777_;
goto v___jp_751_;
}
}
}
default: 
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_x_735_);
lean_ctor_set(v___x_780_, 1, v_x_736_);
v___y_752_ = v___x_780_;
goto v___jp_751_;
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_array_fset(v_xs_x27_750_, v_j_742_, v___y_752_);
lean_dec(v_j_742_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_753_);
v___x_755_ = v___x_746_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_ks_783_; lean_object* v_vs_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_804_; 
v_ks_783_ = lean_ctor_get(v_x_732_, 0);
v_vs_784_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_804_ == 0)
{
v___x_786_ = v_x_732_;
v_isShared_787_ = v_isSharedCheck_804_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_vs_784_);
lean_inc(v_ks_783_);
lean_dec(v_x_732_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_804_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_ks_783_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_vs_784_);
v___x_789_ = v_reuseFailAlloc_803_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v_newNode_790_; uint8_t v___y_792_; size_t v___x_798_; uint8_t v___x_799_; 
v_newNode_790_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_789_, v_x_735_, v_x_736_);
v___x_798_ = ((size_t)7ULL);
v___x_799_ = lean_usize_dec_le(v___x_798_, v_x_734_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_790_);
v___x_801_ = lean_unsigned_to_nat(4u);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
lean_dec(v___x_800_);
v___y_792_ = v___x_802_;
goto v___jp_791_;
}
else
{
v___y_792_ = v___x_799_;
goto v___jp_791_;
}
v___jp_791_:
{
if (v___y_792_ == 0)
{
lean_object* v_ks_793_; lean_object* v_vs_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_ks_793_ = lean_ctor_get(v_newNode_790_, 0);
lean_inc_ref(v_ks_793_);
v_vs_794_ = lean_ctor_get(v_newNode_790_, 1);
lean_inc_ref(v_vs_794_);
lean_dec_ref(v_newNode_790_);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0);
v___x_797_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_734_, v_ks_793_, v_vs_794_, v___x_795_, v___x_796_);
lean_dec_ref(v_vs_794_);
lean_dec_ref(v_ks_793_);
return v___x_797_;
}
else
{
return v_newNode_790_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_805_, lean_object* v_keys_806_, lean_object* v_vals_807_, lean_object* v_i_808_, lean_object* v_entries_809_){
_start:
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = lean_array_get_size(v_keys_806_);
v___x_811_ = lean_nat_dec_lt(v_i_808_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec(v_i_808_);
return v_entries_809_;
}
else
{
lean_object* v_k_812_; lean_object* v_v_813_; uint64_t v___y_815_; 
v_k_812_ = lean_array_fget_borrowed(v_keys_806_, v_i_808_);
v_v_813_ = lean_array_fget_borrowed(v_vals_807_, v_i_808_);
if (lean_obj_tag(v_k_812_) == 0)
{
uint64_t v___x_826_; 
v___x_826_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_815_ = v___x_826_;
goto v___jp_814_;
}
else
{
uint64_t v_hash_827_; 
v_hash_827_ = lean_ctor_get_uint64(v_k_812_, sizeof(void*)*2);
v___y_815_ = v_hash_827_;
goto v___jp_814_;
}
v___jp_814_:
{
size_t v_h_816_; size_t v___x_817_; lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v_h_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_h_816_ = lean_uint64_to_usize(v___y_815_);
v___x_817_ = ((size_t)5ULL);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_sub(v_depth_805_, v___x_819_);
v___x_821_ = lean_usize_mul(v___x_817_, v___x_820_);
v_h_822_ = lean_usize_shift_right(v_h_816_, v___x_821_);
v___x_823_ = lean_nat_add(v_i_808_, v___x_818_);
lean_dec(v_i_808_);
lean_inc(v_v_813_);
lean_inc(v_k_812_);
v___x_824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_809_, v_h_822_, v_depth_805_, v_k_812_, v_v_813_);
v_i_808_ = v___x_823_;
v_entries_809_ = v___x_824_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
size_t v_depth_boxed_833_; lean_object* v_res_834_; 
v_depth_boxed_833_ = lean_unbox_usize(v_depth_828_);
lean_dec(v_depth_828_);
v_res_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_833_, v_keys_829_, v_vals_830_, v_i_831_, v_entries_832_);
lean_dec_ref(v_vals_830_);
lean_dec_ref(v_keys_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_2752__boxed_840_; size_t v_x_2753__boxed_841_; lean_object* v_res_842_; 
v_x_2752__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_x_2753__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_835_, v_x_2752__boxed_840_, v_x_2753__boxed_841_, v_x_838_, v_x_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint64_t v___y_847_; 
if (lean_obj_tag(v_x_844_) == 0)
{
uint64_t v___x_851_; 
v___x_851_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_847_ = v___x_851_;
goto v___jp_846_;
}
else
{
uint64_t v_hash_852_; 
v_hash_852_ = lean_ctor_get_uint64(v_x_844_, sizeof(void*)*2);
v___y_847_ = v_hash_852_;
goto v___jp_846_;
}
v___jp_846_:
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_uint64_to_usize(v___y_847_);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_843_, v___x_848_, v___x_849_, v_x_844_, v_x_845_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object* v_xs_853_, lean_object* v_v_854_, lean_object* v_i_855_){
_start:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_array_get_size(v_xs_853_);
v___x_857_ = lean_nat_dec_lt(v_i_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec(v_i_855_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
else
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_array_fget_borrowed(v_xs_853_, v_i_855_);
v___x_860_ = lean_name_eq(v___x_859_, v_v_854_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_i_855_, v___x_861_);
lean_dec(v_i_855_);
v_i_855_ = v___x_862_;
goto _start;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_i_855_);
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_xs_865_, lean_object* v_v_866_, lean_object* v_i_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_865_, v_v_866_, v_i_867_);
lean_dec(v_v_866_);
lean_dec_ref(v_xs_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object* v_xs_869_, lean_object* v_v_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_869_, v_v_870_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object* v_xs_873_, lean_object* v_v_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_873_, v_v_874_);
lean_dec(v_v_874_);
lean_dec_ref(v_xs_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object* v_x_876_, size_t v_x_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_object* v_es_879_; lean_object* v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; lean_object* v_j_884_; lean_object* v_entry_885_; 
v_es_879_ = lean_ctor_get(v_x_876_, 0);
v___x_880_ = lean_box(2);
v___x_881_ = ((size_t)5ULL);
v___x_882_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_883_ = lean_usize_land(v_x_877_, v___x_882_);
v_j_884_ = lean_usize_to_nat(v___x_883_);
v_entry_885_ = lean_array_get(v___x_880_, v_es_879_, v_j_884_);
switch(lean_obj_tag(v_entry_885_))
{
case 0:
{
lean_object* v_key_886_; uint8_t v___x_887_; 
v_key_886_ = lean_ctor_get(v_entry_885_, 0);
lean_inc(v_key_886_);
lean_dec_ref(v_entry_885_);
v___x_887_ = lean_name_eq(v_x_878_, v_key_886_);
lean_dec(v_key_886_);
if (v___x_887_ == 0)
{
lean_dec(v_j_884_);
return v_x_876_;
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
lean_inc_ref(v_es_879_);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_x_876_, 0);
lean_dec(v_unused_896_);
v___x_889_ = v_x_876_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_x_876_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_array_set(v_es_879_, v_j_884_, v___x_880_);
lean_dec(v_j_884_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
case 1:
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_930_; 
lean_inc_ref(v_es_879_);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_x_876_, 0);
lean_dec(v_unused_931_);
v___x_898_ = v_x_876_;
v_isShared_899_ = v_isSharedCheck_930_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_x_876_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_930_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_node_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_929_; 
v_node_900_ = lean_ctor_get(v_entry_885_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_entry_885_);
if (v_isSharedCheck_929_ == 0)
{
v___x_902_ = v_entry_885_;
v_isShared_903_ = v_isSharedCheck_929_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_node_900_);
lean_dec(v_entry_885_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_929_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_entries_904_; size_t v___x_905_; lean_object* v_newNode_906_; lean_object* v___x_907_; 
v_entries_904_ = lean_array_set(v_es_879_, v_j_884_, v___x_880_);
v___x_905_ = lean_usize_shift_right(v_x_877_, v___x_881_);
v_newNode_906_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_900_, v___x_905_, v_x_878_);
lean_inc_ref(v_newNode_906_);
v___x_907_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_909_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v_newNode_906_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_newNode_906_);
v___x_909_ = v_reuseFailAlloc_914_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_array_set(v_entries_904_, v_j_884_, v___x_909_);
lean_dec(v_j_884_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_910_);
v___x_912_ = v___x_898_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_val_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_newNode_906_);
lean_del_object(v___x_902_);
v_val_915_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_val_915_);
lean_dec_ref(v___x_907_);
v_fst_916_ = lean_ctor_get(v_val_915_, 0);
v_snd_917_ = lean_ctor_get(v_val_915_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_val_915_);
if (v_isSharedCheck_928_ == 0)
{
v___x_919_ = v_val_915_;
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_snd_917_);
lean_inc(v_fst_916_);
lean_dec(v_val_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_fst_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_917_);
v___x_922_ = v_reuseFailAlloc_927_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_array_set(v_entries_904_, v_j_884_, v___x_922_);
lean_dec(v_j_884_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_923_);
v___x_925_ = v___x_898_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_884_);
return v_x_876_;
}
}
}
else
{
lean_object* v_ks_932_; lean_object* v_vs_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_ks_932_ = lean_ctor_get(v_x_876_, 0);
v_vs_933_ = lean_ctor_get(v_x_876_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_x_876_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_vs_933_);
lean_inc(v_ks_932_);
lean_dec(v_x_876_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; 
v___x_937_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_932_, v_x_878_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_939_; 
if (v_isShared_936_ == 0)
{
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_ks_932_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_vs_933_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
lean_object* v_val_941_; lean_object* v_keys_x27_942_; lean_object* v_vals_x27_943_; lean_object* v___x_945_; 
v_val_941_ = lean_ctor_get(v___x_937_, 0);
lean_inc_n(v_val_941_, 2);
lean_dec_ref(v___x_937_);
v_keys_x27_942_ = l_Array_eraseIdx___redArg(v_ks_932_, v_val_941_);
v_vals_x27_943_ = l_Array_eraseIdx___redArg(v_vs_933_, v_val_941_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v_vals_x27_943_);
lean_ctor_set(v___x_935_, 0, v_keys_x27_942_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_keys_x27_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_vals_x27_943_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_2961__boxed_951_; lean_object* v_res_952_; 
v_x_2961__boxed_951_ = lean_unbox_usize(v_x_949_);
lean_dec(v_x_949_);
v_res_952_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_948_, v_x_2961__boxed_951_, v_x_950_);
lean_dec(v_x_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
uint64_t v___y_956_; 
if (lean_obj_tag(v_x_954_) == 0)
{
uint64_t v___x_959_; 
v___x_959_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_956_ = v___x_959_;
goto v___jp_955_;
}
else
{
uint64_t v_hash_960_; 
v_hash_960_ = lean_ctor_get_uint64(v_x_954_, sizeof(void*)*2);
v___y_956_ = v_hash_960_;
goto v___jp_955_;
}
v___jp_955_:
{
size_t v_h_957_; lean_object* v___x_958_; 
v_h_957_ = lean_uint64_to_usize(v___y_956_);
v___x_958_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_953_, v_h_957_, v_x_954_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_961_, v_x_962_);
lean_dec(v_x_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object* v_s_964_, lean_object* v_keys_965_, lean_object* v_declName_966_, uint8_t v_phase_967_, lean_object* v_proc_968_){
_start:
{
lean_object* v_pre_969_; lean_object* v_eval_970_; lean_object* v_post_971_; lean_object* v_simprocNames_972_; lean_object* v_erased_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_994_; 
v_pre_969_ = lean_ctor_get(v_s_964_, 0);
v_eval_970_ = lean_ctor_get(v_s_964_, 1);
v_post_971_ = lean_ctor_get(v_s_964_, 2);
v_simprocNames_972_ = lean_ctor_get(v_s_964_, 3);
v_erased_973_ = lean_ctor_get(v_s_964_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v_s_964_);
if (v_isSharedCheck_994_ == 0)
{
v___x_975_ = v_s_964_;
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_erased_973_);
lean_inc(v_simprocNames_972_);
lean_inc(v_post_971_);
lean_inc(v_eval_970_);
lean_inc(v_pre_969_);
lean_dec(v_s_964_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v_entry_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc_ref(v_keys_965_);
lean_inc_n(v_declName_966_, 2);
v___x_977_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_977_, 0, v_declName_966_);
lean_ctor_set(v___x_977_, 1, v_keys_965_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*2, v_phase_967_);
v_entry_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_entry_978_, 0, v___x_977_);
lean_ctor_set(v_entry_978_, 1, v_proc_968_);
v___x_979_ = lean_box(0);
v___x_980_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_972_, v_declName_966_, v___x_979_);
v___x_981_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_973_, v_declName_966_);
lean_dec(v_declName_966_);
switch(v_phase_967_)
{
case 0:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_969_, v_keys_965_, v_entry_978_);
lean_dec_ref(v_keys_965_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v___x_981_);
lean_ctor_set(v___x_975_, 3, v___x_980_);
lean_ctor_set(v___x_975_, 0, v___x_982_);
v___x_984_ = v___x_975_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_eval_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_post_971_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___x_981_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
case 1:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_970_, v_keys_965_, v_entry_978_);
lean_dec_ref(v_keys_965_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v___x_981_);
lean_ctor_set(v___x_975_, 3, v___x_980_);
lean_ctor_set(v___x_975_, 1, v___x_986_);
v___x_988_ = v___x_975_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_pre_969_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_post_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v___x_981_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
default: 
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_971_, v_keys_965_, v_entry_978_);
lean_dec_ref(v_keys_965_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v___x_981_);
lean_ctor_set(v___x_975_, 3, v___x_980_);
lean_ctor_set(v___x_975_, 2, v___x_990_);
v___x_992_ = v___x_975_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_pre_969_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_eval_970_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v___x_981_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object* v_s_995_, lean_object* v_keys_996_, lean_object* v_declName_997_, lean_object* v_phase_998_, lean_object* v_proc_999_){
_start:
{
uint8_t v_phase_boxed_1000_; lean_object* v_res_1001_; 
v_phase_boxed_1000_ = lean_unbox(v_phase_998_);
v_res_1001_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_995_, v_keys_996_, v_declName_997_, v_phase_boxed_1000_, v_proc_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object* v_00_u03b2_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_1003_, v_x_1004_, v_x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1008_, v_x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object* v_00_u03b2_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(v_00_u03b2_1011_, v_x_1012_, v_x_1013_);
lean_dec(v_x_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_1015_, lean_object* v_x_1016_, size_t v_x_1017_, size_t v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1016_, v_x_1017_, v_x_1018_, v_x_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
size_t v_x_3172__boxed_1028_; size_t v_x_3173__boxed_1029_; lean_object* v_res_1030_; 
v_x_3172__boxed_1028_ = lean_unbox_usize(v_x_1024_);
lean_dec(v_x_1024_);
v_x_3173__boxed_1029_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1030_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_1022_, v_x_1023_, v_x_3172__boxed_1028_, v_x_3173__boxed_1029_, v_x_1026_, v_x_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object* v_00_u03b2_1031_, lean_object* v_x_1032_, size_t v_x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1032_, v_x_1033_, v_x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
size_t v_x_3189__boxed_1040_; lean_object* v_res_1041_; 
v_x_3189__boxed_1040_ = lean_unbox_usize(v_x_1038_);
lean_dec(v_x_1038_);
v_res_1041_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_1036_, v_x_1037_, v_x_3189__boxed_1040_, v_x_1039_);
lean_dec(v_x_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_00_u03b2_1046_, v_x_1047_, v_x_1048_);
lean_dec(v_x_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_x_1051_, v_x_1052_, v_x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1055_, lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_1056_, v_k_1057_, v_v_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1060_, size_t v_depth_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_entries_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_1061_, v_keys_1062_, v_vals_1063_, v_i_1065_, v_entries_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, size_t v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
size_t v_x_3220__boxed_1086_; lean_object* v_res_1087_; 
v_x_3220__boxed_1086_ = lean_unbox_usize(v_x_1084_);
lean_dec(v_x_1084_);
v_res_1087_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v_00_u03b2_1082_, v_x_1083_, v_x_3220__boxed_1086_, v_x_1085_);
lean_dec(v_x_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, size_t v_x_1090_, size_t v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_, v_x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
size_t v_x_3231__boxed_1101_; size_t v_x_3232__boxed_1102_; lean_object* v_res_1103_; 
v_x_3231__boxed_1101_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_x_3232__boxed_1102_ = lean_unbox_usize(v_x_1098_);
lean_dec(v_x_1098_);
v_res_1103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(v_00_u03b2_1095_, v_x_1096_, v_x_3231__boxed_1101_, v_x_3232__boxed_1102_, v_x_1099_, v_x_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1110_, lean_object* v_keys_1111_, lean_object* v_vals_1112_, lean_object* v_heq_1113_, lean_object* v_i_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_keys_1111_, v_vals_1112_, v_i_1114_, v_k_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_heq_1120_, lean_object* v_i_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(v_00_u03b2_1117_, v_keys_1118_, v_vals_1119_, v_heq_1120_, v_i_1121_, v_k_1122_);
lean_dec(v_k_1122_);
lean_dec_ref(v_vals_1119_);
lean_dec_ref(v_keys_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15(lean_object* v_00_u03b2_1124_, lean_object* v_n_1125_, lean_object* v_k_1126_, lean_object* v_v_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(v_n_1125_, v_k_1126_, v_v_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_1129_, size_t v_depth_1130_, lean_object* v_keys_1131_, lean_object* v_vals_1132_, lean_object* v_heq_1133_, lean_object* v_i_1134_, lean_object* v_entries_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_depth_1130_, v_keys_1131_, v_vals_1132_, v_i_1134_, v_entries_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_1137_, lean_object* v_depth_1138_, lean_object* v_keys_1139_, lean_object* v_vals_1140_, lean_object* v_heq_1141_, lean_object* v_i_1142_, lean_object* v_entries_1143_){
_start:
{
size_t v_depth_boxed_1144_; lean_object* v_res_1145_; 
v_depth_boxed_1144_ = lean_unbox_usize(v_depth_1138_);
lean_dec(v_depth_1138_);
v_res_1145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(v_00_u03b2_1137_, v_depth_boxed_1144_, v_keys_1139_, v_vals_1140_, v_heq_1141_, v_i_1142_, v_entries_1143_);
lean_dec_ref(v_vals_1140_);
lean_dec_ref(v_keys_1139_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(lean_object* v_x_1146_, lean_object* v_keys_1147_, lean_object* v_v_1148_, lean_object* v_k_1149_, lean_object* v_as_1150_, lean_object* v_k_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_1146_, v_keys_1147_, v_v_1148_, v_k_1149_, v_as_1150_, v_k_1151_, v_x_1152_, v_x_1153_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___boxed(lean_object* v_x_1157_, lean_object* v_keys_1158_, lean_object* v_v_1159_, lean_object* v_k_1160_, lean_object* v_as_1161_, lean_object* v_k_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(v_x_1157_, v_keys_1158_, v_v_1159_, v_k_1160_, v_as_1161_, v_k_1162_, v_x_1163_, v_x_1164_, v_x_1165_, v_x_1166_);
lean_dec_ref(v_k_1162_);
lean_dec_ref(v_keys_1158_);
lean_dec(v_x_1157_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17(lean_object* v_00_u03b2_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(v_x_1169_, v_x_1170_, v_x_1171_, v_x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object* v_s_1174_, lean_object* v_declName_1175_){
_start:
{
lean_object* v_pre_1176_; lean_object* v_eval_1177_; lean_object* v_post_1178_; lean_object* v_simprocNames_1179_; lean_object* v_erased_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1190_; 
v_pre_1176_ = lean_ctor_get(v_s_1174_, 0);
v_eval_1177_ = lean_ctor_get(v_s_1174_, 1);
v_post_1178_ = lean_ctor_get(v_s_1174_, 2);
v_simprocNames_1179_ = lean_ctor_get(v_s_1174_, 3);
v_erased_1180_ = lean_ctor_get(v_s_1174_, 4);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_s_1174_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1182_ = v_s_1174_;
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_erased_1180_);
lean_inc(v_simprocNames_1179_);
lean_inc(v_post_1178_);
lean_inc(v_eval_1177_);
lean_inc(v_pre_1176_);
lean_dec(v_s_1174_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1184_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_1179_, v_declName_1175_);
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_1180_, v_declName_1175_, v___x_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 4, v___x_1186_);
lean_ctor_set(v___x_1182_, 3, v___x_1184_);
v___x_1188_ = v___x_1182_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_pre_1176_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_eval_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_post_1178_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_unsigned_to_nat(16u);
v___x_1193_ = lean_mk_array(v___x_1192_, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0);
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default(void){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs(void){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1203_ = lean_st_mk_ref(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object* v_a_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
else
{
lean_object* v_key_1210_; lean_object* v_tail_1211_; uint8_t v___x_1212_; 
v_key_1210_ = lean_ctor_get(v_x_1208_, 0);
v_tail_1211_ = lean_ctor_get(v_x_1208_, 2);
v___x_1212_ = lean_name_eq(v_key_1210_, v_a_1207_);
if (v___x_1212_ == 0)
{
v_x_1208_ = v_tail_1211_;
goto _start;
}
else
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_1214_, lean_object* v_x_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1214_, v_x_1215_);
lean_dec(v_x_1215_);
lean_dec(v_a_1214_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_buckets_1220_; lean_object* v___x_1221_; uint64_t v___y_1223_; 
v_buckets_1220_ = lean_ctor_get(v_m_1218_, 1);
v___x_1221_ = lean_array_get_size(v_buckets_1220_);
if (lean_obj_tag(v_a_1219_) == 0)
{
uint64_t v___x_1237_; 
v___x_1237_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1223_ = v___x_1237_;
goto v___jp_1222_;
}
else
{
uint64_t v_hash_1238_; 
v_hash_1238_ = lean_ctor_get_uint64(v_a_1219_, sizeof(void*)*2);
v___y_1223_ = v_hash_1238_;
goto v___jp_1222_;
}
v___jp_1222_:
{
uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v_fold_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1224_ = 32ULL;
v___x_1225_ = lean_uint64_shift_right(v___y_1223_, v___x_1224_);
v_fold_1226_ = lean_uint64_xor(v___y_1223_, v___x_1225_);
v___x_1227_ = 16ULL;
v___x_1228_ = lean_uint64_shift_right(v_fold_1226_, v___x_1227_);
v___x_1229_ = lean_uint64_xor(v_fold_1226_, v___x_1228_);
v___x_1230_ = lean_uint64_to_usize(v___x_1229_);
v___x_1231_ = lean_usize_of_nat(v___x_1221_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_sub(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_usize_land(v___x_1230_, v___x_1233_);
v___x_1235_ = lean_array_uget_borrowed(v_buckets_1220_, v___x_1234_);
v___x_1236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1219_, v___x_1235_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object* v_m_1239_, lean_object* v_a_1240_){
_start:
{
uint8_t v_res_1241_; lean_object* v_r_1242_; 
v_res_1241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_m_1239_);
v_r_1242_ = lean_box(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object* v_a_1243_, lean_object* v_b_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_dec(v_b_1244_);
lean_dec(v_a_1243_);
return v_x_1245_;
}
else
{
lean_object* v_key_1246_; lean_object* v_value_1247_; lean_object* v_tail_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1260_; 
v_key_1246_ = lean_ctor_get(v_x_1245_, 0);
v_value_1247_ = lean_ctor_get(v_x_1245_, 1);
v_tail_1248_ = lean_ctor_get(v_x_1245_, 2);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1250_ = v_x_1245_;
v_isShared_1251_ = v_isSharedCheck_1260_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_tail_1248_);
lean_inc(v_value_1247_);
lean_inc(v_key_1246_);
lean_dec(v_x_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1260_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_name_eq(v_key_1246_, v_a_1243_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1243_, v_b_1244_, v_tail_1248_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 2, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_key_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_value_1247_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1258_; 
lean_dec(v_value_1247_);
lean_dec(v_key_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_b_1244_);
lean_ctor_set(v___x_1250_, 0, v_a_1243_);
v___x_1258_ = v___x_1250_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_b_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_tail_1248_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
return v_x_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1291_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1262_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1267_ = v_x_1262_;
v_isShared_1268_ = v_isSharedCheck_1291_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_tail_1265_);
lean_inc(v_value_1264_);
lean_inc(v_key_1263_);
lean_dec(v_x_1262_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1291_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint64_t v___y_1271_; 
v___x_1269_ = lean_array_get_size(v_x_1261_);
if (lean_obj_tag(v_key_1263_) == 0)
{
uint64_t v___x_1289_; 
v___x_1289_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1271_ = v___x_1289_;
goto v___jp_1270_;
}
else
{
uint64_t v_hash_1290_; 
v_hash_1290_ = lean_ctor_get_uint64(v_key_1263_, sizeof(void*)*2);
v___y_1271_ = v_hash_1290_;
goto v___jp_1270_;
}
v___jp_1270_:
{
uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v_fold_1274_; uint64_t v___x_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1272_ = 32ULL;
v___x_1273_ = lean_uint64_shift_right(v___y_1271_, v___x_1272_);
v_fold_1274_ = lean_uint64_xor(v___y_1271_, v___x_1273_);
v___x_1275_ = 16ULL;
v___x_1276_ = lean_uint64_shift_right(v_fold_1274_, v___x_1275_);
v___x_1277_ = lean_uint64_xor(v_fold_1274_, v___x_1276_);
v___x_1278_ = lean_uint64_to_usize(v___x_1277_);
v___x_1279_ = lean_usize_of_nat(v___x_1269_);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_sub(v___x_1279_, v___x_1280_);
v___x_1282_ = lean_usize_land(v___x_1278_, v___x_1281_);
v___x_1283_ = lean_array_uget_borrowed(v_x_1261_, v___x_1282_);
lean_inc(v___x_1283_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 2, v___x_1283_);
v___x_1285_ = v___x_1267_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_key_1263_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_value_1264_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_array_uset(v_x_1261_, v___x_1282_, v___x_1285_);
v_x_1261_ = v___x_1286_;
v_x_1262_ = v_tail_1265_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1292_, lean_object* v_source_1293_, lean_object* v_target_1294_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_array_get_size(v_source_1293_);
v___x_1296_ = lean_nat_dec_lt(v_i_1292_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_source_1293_);
lean_dec(v_i_1292_);
return v_target_1294_;
}
else
{
lean_object* v_es_1297_; lean_object* v___x_1298_; lean_object* v_source_1299_; lean_object* v_target_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_es_1297_ = lean_array_fget(v_source_1293_, v_i_1292_);
v___x_1298_ = lean_box(0);
v_source_1299_ = lean_array_fset(v_source_1293_, v_i_1292_, v___x_1298_);
v_target_1300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1294_, v_es_1297_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v_i_1292_, v___x_1301_);
lean_dec(v_i_1292_);
v_i_1292_ = v___x_1302_;
v_source_1293_ = v_source_1299_;
v_target_1294_ = v_target_1300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object* v_data_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_nbuckets_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1305_ = lean_array_get_size(v_data_1304_);
v___x_1306_ = lean_unsigned_to_nat(2u);
v_nbuckets_1307_ = lean_nat_mul(v___x_1305_, v___x_1306_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_mk_array(v_nbuckets_1307_, v___x_1309_);
v___x_1311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v___x_1308_, v_data_1304_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object* v_m_1312_, lean_object* v_a_1313_, lean_object* v_b_1314_){
_start:
{
lean_object* v_size_1315_; lean_object* v_buckets_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1362_; 
v_size_1315_ = lean_ctor_get(v_m_1312_, 0);
v_buckets_1316_ = lean_ctor_get(v_m_1312_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_m_1312_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1318_ = v_m_1312_;
v_isShared_1319_ = v_isSharedCheck_1362_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_buckets_1316_);
lean_inc(v_size_1315_);
lean_dec(v_m_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1362_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; uint64_t v___y_1322_; 
v___x_1320_ = lean_array_get_size(v_buckets_1316_);
if (lean_obj_tag(v_a_1313_) == 0)
{
uint64_t v___x_1360_; 
v___x_1360_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1322_ = v___x_1360_;
goto v___jp_1321_;
}
else
{
uint64_t v_hash_1361_; 
v_hash_1361_ = lean_ctor_get_uint64(v_a_1313_, sizeof(void*)*2);
v___y_1322_ = v_hash_1361_;
goto v___jp_1321_;
}
v___jp_1321_:
{
uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v_fold_1325_; uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v_bkt_1334_; uint8_t v___x_1335_; 
v___x_1323_ = 32ULL;
v___x_1324_ = lean_uint64_shift_right(v___y_1322_, v___x_1323_);
v_fold_1325_ = lean_uint64_xor(v___y_1322_, v___x_1324_);
v___x_1326_ = 16ULL;
v___x_1327_ = lean_uint64_shift_right(v_fold_1325_, v___x_1326_);
v___x_1328_ = lean_uint64_xor(v_fold_1325_, v___x_1327_);
v___x_1329_ = lean_uint64_to_usize(v___x_1328_);
v___x_1330_ = lean_usize_of_nat(v___x_1320_);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_sub(v___x_1330_, v___x_1331_);
v___x_1333_ = lean_usize_land(v___x_1329_, v___x_1332_);
v_bkt_1334_ = lean_array_uget_borrowed(v_buckets_1316_, v___x_1333_);
v___x_1335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1313_, v_bkt_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v_size_x27_1337_; lean_object* v___x_1338_; lean_object* v_buckets_x27_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
v_size_x27_1337_ = lean_nat_add(v_size_1315_, v___x_1336_);
lean_dec(v_size_1315_);
lean_inc(v_bkt_1334_);
v___x_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1313_);
lean_ctor_set(v___x_1338_, 1, v_b_1314_);
lean_ctor_set(v___x_1338_, 2, v_bkt_1334_);
v_buckets_x27_1339_ = lean_array_uset(v_buckets_1316_, v___x_1333_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(4u);
v___x_1341_ = lean_nat_mul(v_size_x27_1337_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(3u);
v___x_1343_ = lean_nat_div(v___x_1341_, v___x_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_array_get_size(v_buckets_x27_1339_);
v___x_1345_ = lean_nat_dec_le(v___x_1343_, v___x_1344_);
lean_dec(v___x_1343_);
if (v___x_1345_ == 0)
{
lean_object* v_val_1346_; lean_object* v___x_1348_; 
v_val_1346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_buckets_x27_1339_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_val_1346_);
lean_ctor_set(v___x_1318_, 0, v_size_x27_1337_);
v___x_1348_ = v___x_1318_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_size_x27_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_val_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_object* v___x_1351_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_buckets_x27_1339_);
lean_ctor_set(v___x_1318_, 0, v_size_x27_1337_);
v___x_1351_ = v___x_1318_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_size_x27_1337_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_buckets_x27_1339_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v_buckets_x27_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_inc(v_bkt_1334_);
v___x_1353_ = lean_box(0);
v_buckets_x27_1354_ = lean_array_uset(v_buckets_1316_, v___x_1333_, v___x_1353_);
v___x_1355_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1313_, v_b_1314_, v_bkt_1334_);
v___x_1356_ = lean_array_uset(v_buckets_x27_1354_, v___x_1333_, v___x_1355_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1356_);
v___x_1358_ = v___x_1318_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_size_1315_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0));
v___x_1365_ = lean_mk_io_user_error(v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object* v_declName_1368_, lean_object* v_keys_1369_, lean_object* v_proc_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1412_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1412_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1412_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v_proc_1370_);
lean_dec_ref(v_keys_1369_);
lean_dec(v_declName_1368_);
v___x_1378_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 1);
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_keys_1384_; uint8_t v___x_1385_; 
v___x_1382_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_1383_ = lean_st_ref_get(v___x_1382_);
v_keys_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_keys_1384_);
lean_dec(v___x_1383_);
v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_1384_, v_declName_1368_);
lean_dec_ref(v_keys_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v_keys_1387_; lean_object* v_procs_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v___x_1386_ = lean_st_ref_take(v___x_1382_);
v_keys_1387_ = lean_ctor_get(v___x_1386_, 0);
v_procs_1388_ = lean_ctor_get(v___x_1386_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1390_ = v___x_1386_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_procs_1388_);
lean_inc(v_keys_1387_);
lean_dec(v___x_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_inc(v_declName_1368_);
v___x_1392_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_1387_, v_declName_1368_, v_keys_1369_);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_1388_, v_declName_1368_, v_proc_1370_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1393_);
lean_ctor_set(v___x_1390_, 0, v___x_1392_);
v___x_1395_ = v___x_1390_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_st_ref_set(v___x_1382_, v___x_1395_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1396_);
v___x_1398_ = v___x_1375_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_proc_1370_);
lean_dec_ref(v_keys_1369_);
v___x_1402_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2));
v___x_1403_ = l_Lean_privateToUserName(v_declName_1368_);
v___x_1404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1403_, v___x_1385_);
v___x_1405_ = lean_string_append(v___x_1402_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
v___x_1408_ = lean_mk_io_user_error(v___x_1407_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 1);
lean_ctor_set(v___x_1375_, 0, v___x_1408_);
v___x_1410_ = v___x_1375_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
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
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_proc_1370_);
lean_dec_ref(v_keys_1369_);
lean_dec(v_declName_1368_);
v_a_1413_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1372_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1372_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object* v_declName_1421_, lean_object* v_keys_1422_, lean_object* v_proc_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1421_, v_keys_1422_, v_proc_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1427_, v_a_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
uint8_t v_res_1433_; lean_object* v_r_1434_; 
v_res_1433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_1430_, v_m_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_m_1431_);
v_r_1434_ = lean_box(v_res_1433_);
return v_r_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1436_, v_a_1437_, v_b_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object* v_00_u03b2_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1441_, v_x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_a_1445_, lean_object* v_x_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_1444_, v_a_1445_, v_x_1446_);
lean_dec(v_x_1446_);
lean_dec(v_a_1445_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object* v_00_u03b2_1449_, lean_object* v_data_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_data_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object* v_00_u03b2_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v_x_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1453_, v_b_1454_, v_x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1457_, lean_object* v_i_1458_, lean_object* v_source_1459_, lean_object* v_target_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v_i_1458_, v_source_1459_, v_target_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object* v_d_u2081_1473_, lean_object* v_d_u2082_1474_){
_start:
{
lean_object* v_declName_1475_; lean_object* v_declName_1476_; uint8_t v___x_1477_; 
v_declName_1475_ = lean_ctor_get(v_d_u2081_1473_, 0);
v_declName_1476_ = lean_ctor_get(v_d_u2082_1474_, 0);
v___x_1477_ = l_Lean_Name_quickLt(v_declName_1475_, v_declName_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object* v_d_u2081_1478_, lean_object* v_d_u2082_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1478_, v_d_u2082_1479_);
lean_dec_ref(v_d_u2082_1479_);
lean_dec_ref(v_d_u2081_1478_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
v___x_1486_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState(void){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_s_1490_, lean_object* v_d_1491_){
_start:
{
lean_object* v_builtin_1492_; lean_object* v_newEntries_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1503_; 
v_builtin_1492_ = lean_ctor_get(v_s_1490_, 0);
v_newEntries_1493_ = lean_ctor_get(v_s_1490_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_s_1490_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1495_ = v_s_1490_;
v_isShared_1496_ = v_isSharedCheck_1503_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_newEntries_1493_);
lean_inc(v_builtin_1492_);
lean_dec(v_s_1490_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1503_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_declName_1497_; lean_object* v_keys_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v_declName_1497_ = lean_ctor_get(v_d_1491_, 0);
lean_inc(v_declName_1497_);
v_keys_1498_ = lean_ctor_get(v_d_1491_, 1);
lean_inc_ref(v_keys_1498_);
lean_dec_ref(v_d_1491_);
v___x_1499_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_1493_, v_declName_1497_, v_keys_1498_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1499_);
v___x_1501_ = v___x_1495_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_builtin_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1499_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_result_1504_, lean_object* v_declName_1505_, lean_object* v_keys_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_declName_1505_);
lean_ctor_set(v___x_1507_, 1, v_keys_1506_);
v___x_1508_ = lean_array_push(v_result_1504_, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_1509_, lean_object* v_x1_1510_, lean_object* v_x2_1511_, lean_object* v_x3_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_apply_3(v_f_1509_, v_x1_1510_, v_x2_1511_, v_x3_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_1514_, lean_object* v_keys_1515_, lean_object* v_vals_1516_, lean_object* v_i_1517_, lean_object* v_acc_1518_){
_start:
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = lean_array_get_size(v_keys_1515_);
v___x_1520_ = lean_nat_dec_lt(v_i_1517_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_dec(v_i_1517_);
lean_dec(v_f_1514_);
return v_acc_1518_;
}
else
{
lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_k_1521_ = lean_array_fget_borrowed(v_keys_1515_, v_i_1517_);
v_v_1522_ = lean_array_fget_borrowed(v_vals_1516_, v_i_1517_);
lean_inc(v_f_1514_);
lean_inc(v_v_1522_);
lean_inc(v_k_1521_);
v___x_1523_ = lean_apply_3(v_f_1514_, v_acc_1518_, v_k_1521_, v_v_1522_);
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = lean_nat_add(v_i_1517_, v___x_1524_);
lean_dec(v_i_1517_);
v_i_1517_ = v___x_1525_;
v_acc_1518_ = v___x_1523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_1527_, lean_object* v_keys_1528_, lean_object* v_vals_1529_, lean_object* v_i_1530_, lean_object* v_acc_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1527_, v_keys_1528_, v_vals_1529_, v_i_1530_, v_acc_1531_);
lean_dec_ref(v_vals_1529_);
lean_dec_ref(v_keys_1528_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
if (lean_obj_tag(v_x_1534_) == 0)
{
lean_object* v_es_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_es_1536_ = lean_ctor_get(v_x_1534_, 0);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_array_get_size(v_es_1536_);
v___x_1539_ = lean_nat_dec_lt(v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_dec(v_f_1533_);
return v_x_1535_;
}
else
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_nat_dec_le(v___x_1538_, v___x_1538_);
if (v___x_1540_ == 0)
{
if (v___x_1539_ == 0)
{
lean_dec(v_f_1533_);
return v_x_1535_;
}
else
{
size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = lean_usize_of_nat(v___x_1538_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1533_, v_es_1536_, v___x_1541_, v___x_1542_, v_x_1535_);
return v___x_1543_;
}
}
else
{
size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = lean_usize_of_nat(v___x_1538_);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1533_, v_es_1536_, v___x_1544_, v___x_1545_, v_x_1535_);
return v___x_1546_;
}
}
}
else
{
lean_object* v_ks_1547_; lean_object* v_vs_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_ks_1547_ = lean_ctor_get(v_x_1534_, 0);
v_vs_1548_ = lean_ctor_get(v_x_1534_, 1);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1533_, v_ks_1547_, v_vs_1548_, v___x_1549_, v_x_1535_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1551_, lean_object* v_as_1552_, size_t v_i_1553_, size_t v_stop_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v___y_1557_; uint8_t v___x_1561_; 
v___x_1561_ = lean_usize_dec_eq(v_i_1553_, v_stop_1554_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_array_uget_borrowed(v_as_1552_, v_i_1553_);
switch(lean_obj_tag(v___x_1562_))
{
case 0:
{
lean_object* v_key_1563_; lean_object* v_val_1564_; lean_object* v___x_1565_; 
v_key_1563_ = lean_ctor_get(v___x_1562_, 0);
v_val_1564_ = lean_ctor_get(v___x_1562_, 1);
lean_inc(v_f_1551_);
lean_inc(v_val_1564_);
lean_inc(v_key_1563_);
v___x_1565_ = lean_apply_3(v_f_1551_, v_b_1555_, v_key_1563_, v_val_1564_);
v___y_1557_ = v___x_1565_;
goto v___jp_1556_;
}
case 1:
{
lean_object* v_node_1566_; lean_object* v___x_1567_; 
v_node_1566_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_f_1551_);
v___x_1567_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1551_, v_node_1566_, v_b_1555_);
v___y_1557_ = v___x_1567_;
goto v___jp_1556_;
}
default: 
{
v___y_1557_ = v_b_1555_;
goto v___jp_1556_;
}
}
}
else
{
lean_dec(v_f_1551_);
return v_b_1555_;
}
v___jp_1556_:
{
size_t v___x_1558_; size_t v___x_1559_; 
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1553_, v___x_1558_);
v_i_1553_ = v___x_1559_;
v_b_1555_ = v___y_1557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1568_, lean_object* v_as_1569_, lean_object* v_i_1570_, lean_object* v_stop_1571_, lean_object* v_b_1572_){
_start:
{
size_t v_i_boxed_1573_; size_t v_stop_boxed_1574_; lean_object* v_res_1575_; 
v_i_boxed_1573_ = lean_unbox_usize(v_i_1570_);
lean_dec(v_i_1570_);
v_stop_boxed_1574_ = lean_unbox_usize(v_stop_1571_);
lean_dec(v_stop_1571_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1568_, v_as_1569_, v_i_boxed_1573_, v_stop_boxed_1574_, v_b_1572_);
lean_dec_ref(v_as_1569_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1576_, v_x_1577_, v_x_1578_);
lean_dec_ref(v_x_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_1580_, lean_object* v_f_1581_, lean_object* v_init_1582_){
_start:
{
lean_object* v___f_1583_; lean_object* v___x_1584_; 
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1583_, 0, v_f_1581_);
v___x_1584_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1583_, v_map_1580_, v_init_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_1585_, lean_object* v_f_1586_, lean_object* v_init_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1585_, v_f_1586_, v_init_1587_);
lean_dec_ref(v_map_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_1590_, lean_object* v_lo_1591_, lean_object* v_hi_1592_){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_nat_dec_lt(v_lo_1591_, v_hi_1592_);
if (v___x_1593_ == 0)
{
lean_dec(v_lo_1591_);
return v_as_1590_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; uint8_t v___x_1598_; 
v___x_1594_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_1591_);
v___x_1595_ = l_Array_qpartition___redArg(v_as_1590_, v___x_1594_, v_lo_1591_, v_hi_1592_);
v_fst_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_fst_1596_);
v_snd_1597_ = lean_ctor_get(v___x_1595_, 1);
lean_inc(v_snd_1597_);
lean_dec_ref(v___x_1595_);
v___x_1598_ = lean_nat_dec_le(v_hi_1592_, v_fst_1596_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_snd_1597_, v_lo_1591_, v_fst_1596_);
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = lean_nat_add(v_fst_1596_, v___x_1600_);
lean_dec(v_fst_1596_);
v_as_1590_ = v___x_1599_;
v_lo_1591_ = v___x_1601_;
goto _start;
}
else
{
lean_dec(v_fst_1596_);
lean_dec(v_lo_1591_);
return v_snd_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_1603_, lean_object* v_lo_1604_, lean_object* v_hi_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_as_1603_, v_lo_1604_, v_hi_1605_);
lean_dec(v_hi_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1609_, lean_object* v_s_1610_){
_start:
{
lean_object* v_newEntries_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_result_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_newEntries_1611_ = lean_ctor_get(v_s_1610_, 1);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1614_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1611_, v___f_1609_, v___x_1613_);
v___x_1615_ = lean_array_get_size(v_result_1614_);
v___x_1616_ = lean_nat_dec_eq(v___x_1615_, v___x_1612_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___y_1620_; uint8_t v___x_1624_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_sub(v___x_1615_, v___x_1617_);
v___x_1624_ = lean_nat_dec_le(v___x_1612_, v___x_1618_);
if (v___x_1624_ == 0)
{
lean_inc(v___x_1618_);
v___y_1620_ = v___x_1618_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___x_1612_;
goto v___jp_1619_;
}
v___jp_1619_:
{
uint8_t v___x_1621_; 
v___x_1621_ = lean_nat_dec_le(v___y_1620_, v___x_1618_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_dec(v___x_1618_);
lean_inc(v___y_1620_);
v___x_1622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1614_, v___y_1620_, v___y_1620_);
lean_dec(v___y_1620_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1614_, v___y_1620_, v___x_1618_);
lean_dec(v___x_1618_);
return v___x_1623_;
}
}
}
else
{
return v_result_1614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1625_, lean_object* v_s_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1625_, v_s_1626_);
lean_dec_ref(v_s_1626_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_box(0);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_x_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_1630_);
lean_dec_ref(v_x_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1632_, lean_object* v_x_1633_, lean_object* v_s_1634_){
_start:
{
lean_object* v_newEntries_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_result_1638_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_newEntries_1635_ = lean_ctor_get(v_s_1634_, 1);
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1638_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1635_, v___f_1632_, v___x_1637_);
v___x_1644_ = lean_array_get_size(v_result_1638_);
v___x_1645_ = lean_nat_dec_eq(v___x_1644_, v___x_1636_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___y_1649_; uint8_t v___x_1651_; 
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = lean_nat_sub(v___x_1644_, v___x_1646_);
v___x_1651_ = lean_nat_dec_le(v___x_1636_, v___x_1647_);
if (v___x_1651_ == 0)
{
lean_inc(v___x_1647_);
v___y_1649_ = v___x_1647_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v___x_1636_;
goto v___jp_1648_;
}
v___jp_1648_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_le(v___y_1649_, v___x_1647_);
if (v___x_1650_ == 0)
{
lean_dec(v___x_1647_);
lean_inc(v___y_1649_);
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___y_1649_;
goto v___jp_1639_;
}
else
{
v___y_1640_ = v___y_1649_;
v___y_1641_ = v___x_1647_;
goto v___jp_1639_;
}
}
}
else
{
lean_object* v___x_1652_; 
lean_inc_n(v_result_1638_, 2);
v___x_1652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1652_, 0, v_result_1638_);
lean_ctor_set(v___x_1652_, 1, v_result_1638_);
lean_ctor_set(v___x_1652_, 2, v_result_1638_);
return v___x_1652_;
}
v___jp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1638_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_inc_ref_n(v___x_1642_, 2);
v___x_1643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
lean_ctor_set(v___x_1643_, 2, v___x_1642_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1653_, lean_object* v_x_1654_, lean_object* v_s_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1653_, v_x_1654_, v_s_1655_);
lean_dec_ref(v_s_1655_);
lean_dec_ref(v_x_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v_keys_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1669_; 
v___x_1659_ = lean_st_ref_get(v___x_1657_);
v_keys_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v___x_1659_, 1);
lean_dec(v_unused_1670_);
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_keys_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1669_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_keys_1660_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1671_);
lean_dec(v___x_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1674_, lean_object* v_x_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v_keys_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1688_; 
v___x_1678_ = lean_st_ref_get(v___x_1674_);
v_keys_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1678_, 1);
lean_dec(v_unused_1689_);
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_keys_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_keys_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1690_, v_x_1691_, v___y_1692_);
lean_dec_ref(v___y_1692_);
lean_dec_ref(v_x_1691_);
lean_dec(v___x_1690_);
return v_res_1694_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___f_1710_; 
v___x_1709_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1710_, 0, v___x_1709_);
return v___f_1710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___f_1712_; 
v___x_1711_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1712_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_1712_, 0, v___x_1711_);
return v___f_1712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_box(2);
v___f_1715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___f_1719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1721_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set(v___x_1721_, 1, v___f_1719_);
lean_ctor_set(v___x_1721_, 2, v___f_1718_);
lean_ctor_set(v___x_1721_, 3, v___f_1717_);
lean_ctor_set(v___x_1721_, 4, v___f_1716_);
lean_ctor_set(v___x_1721_, 5, v___f_1715_);
lean_ctor_set(v___x_1721_, 6, v___x_1714_);
lean_ctor_set(v___x_1721_, 7, v___x_1713_);
return v___x_1721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___f_1722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___f_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1727_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_map_1732_, lean_object* v_f_1733_, lean_object* v_init_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1732_, v_f_1733_, v_init_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_map_1738_, lean_object* v_f_1739_, lean_object* v_init_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_1736_, v_00_u03b2_1737_, v_map_1738_, v_f_1739_, v_init_1740_);
lean_dec_ref(v_map_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object* v_n_1742_, lean_object* v_as_1743_, lean_object* v_lo_1744_, lean_object* v_hi_1745_, lean_object* v_w_1746_, lean_object* v_hlo_1747_, lean_object* v_hhi_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_as_1743_, v_lo_1744_, v_hi_1745_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1750_, lean_object* v_as_1751_, lean_object* v_lo_1752_, lean_object* v_hi_1753_, lean_object* v_w_1754_, lean_object* v_hlo_1755_, lean_object* v_hhi_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_1750_, v_as_1751_, v_lo_1752_, v_hi_1753_, v_w_1754_, v_hlo_1755_, v_hhi_1756_);
lean_dec(v_hi_1753_);
lean_dec(v_n_1750_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_1758_, lean_object* v_f_1759_, lean_object* v_init_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1759_, v_map_1758_, v_init_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_1762_, lean_object* v_f_1763_, lean_object* v_init_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1762_, v_f_1763_, v_init_1764_);
lean_dec_ref(v_map_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_1766_, lean_object* v_00_u03b2_1767_, lean_object* v_map_1768_, lean_object* v_f_1769_, lean_object* v_init_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1769_, v_map_1768_, v_init_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_1772_, lean_object* v_00_u03b2_1773_, lean_object* v_map_1774_, lean_object* v_f_1775_, lean_object* v_init_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1772_, v_00_u03b2_1773_, v_map_1774_, v_f_1775_, v_init_1776_);
lean_dec_ref(v_map_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1778_, lean_object* v_00_u03b1_1779_, lean_object* v_00_u03b2_1780_, lean_object* v_f_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1781_, v_x_1782_, v_x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1785_, lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_f_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1785_, v_00_u03b1_1786_, v_00_u03b2_1787_, v_f_1788_, v_x_1789_, v_x_1790_);
lean_dec_ref(v_x_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_00_u03c3_1794_, lean_object* v_f_1795_, lean_object* v_as_1796_, size_t v_i_1797_, size_t v_stop_1798_, lean_object* v_b_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1795_, v_as_1796_, v_i_1797_, v_stop_1798_, v_b_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_00_u03b2_1802_, lean_object* v_00_u03c3_1803_, lean_object* v_f_1804_, lean_object* v_as_1805_, lean_object* v_i_1806_, lean_object* v_stop_1807_, lean_object* v_b_1808_){
_start:
{
size_t v_i_boxed_1809_; size_t v_stop_boxed_1810_; lean_object* v_res_1811_; 
v_i_boxed_1809_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_stop_boxed_1810_ = lean_unbox_usize(v_stop_1807_);
lean_dec(v_stop_1807_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1801_, v_00_u03b2_1802_, v_00_u03c3_1803_, v_f_1804_, v_as_1805_, v_i_boxed_1809_, v_stop_boxed_1810_, v_b_1808_);
lean_dec_ref(v_as_1805_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_1812_, lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_f_1815_, lean_object* v_keys_1816_, lean_object* v_vals_1817_, lean_object* v_heq_1818_, lean_object* v_i_1819_, lean_object* v_acc_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1815_, v_keys_1816_, v_vals_1817_, v_i_1819_, v_acc_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_1822_, lean_object* v_00_u03b1_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_f_1825_, lean_object* v_keys_1826_, lean_object* v_vals_1827_, lean_object* v_heq_1828_, lean_object* v_i_1829_, lean_object* v_acc_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_1822_, v_00_u03b1_1823_, v_00_u03b2_1824_, v_f_1825_, v_keys_1826_, v_vals_1827_, v_heq_1828_, v_i_1829_, v_acc_1830_);
lean_dec_ref(v_vals_1827_);
lean_dec_ref(v_keys_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object* v_a_1832_, lean_object* v_x_1833_){
_start:
{
if (lean_obj_tag(v_x_1833_) == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_box(0);
return v___x_1834_;
}
else
{
lean_object* v_key_1835_; lean_object* v_value_1836_; lean_object* v_tail_1837_; uint8_t v___x_1838_; 
v_key_1835_ = lean_ctor_get(v_x_1833_, 0);
v_value_1836_ = lean_ctor_get(v_x_1833_, 1);
v_tail_1837_ = lean_ctor_get(v_x_1833_, 2);
v___x_1838_ = lean_name_eq(v_key_1835_, v_a_1832_);
if (v___x_1838_ == 0)
{
v_x_1833_ = v_tail_1837_;
goto _start;
}
else
{
lean_object* v___x_1840_; 
lean_inc(v_value_1836_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_value_1836_);
return v___x_1840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1841_, v_x_1842_);
lean_dec(v_x_1842_);
lean_dec(v_a_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_buckets_1846_; lean_object* v___x_1847_; uint64_t v___y_1849_; 
v_buckets_1846_ = lean_ctor_get(v_m_1844_, 1);
v___x_1847_ = lean_array_get_size(v_buckets_1846_);
if (lean_obj_tag(v_a_1845_) == 0)
{
uint64_t v___x_1863_; 
v___x_1863_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1849_ = v___x_1863_;
goto v___jp_1848_;
}
else
{
uint64_t v_hash_1864_; 
v_hash_1864_ = lean_ctor_get_uint64(v_a_1845_, sizeof(void*)*2);
v___y_1849_ = v_hash_1864_;
goto v___jp_1848_;
}
v___jp_1848_:
{
uint64_t v___x_1850_; uint64_t v___x_1851_; uint64_t v_fold_1852_; uint64_t v___x_1853_; uint64_t v___x_1854_; uint64_t v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1850_ = 32ULL;
v___x_1851_ = lean_uint64_shift_right(v___y_1849_, v___x_1850_);
v_fold_1852_ = lean_uint64_xor(v___y_1849_, v___x_1851_);
v___x_1853_ = 16ULL;
v___x_1854_ = lean_uint64_shift_right(v_fold_1852_, v___x_1853_);
v___x_1855_ = lean_uint64_xor(v_fold_1852_, v___x_1854_);
v___x_1856_ = lean_uint64_to_usize(v___x_1855_);
v___x_1857_ = lean_usize_of_nat(v___x_1847_);
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = lean_usize_sub(v___x_1857_, v___x_1858_);
v___x_1860_ = lean_usize_land(v___x_1856_, v___x_1859_);
v___x_1861_ = lean_array_uget_borrowed(v_buckets_1846_, v___x_1860_);
v___x_1862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1845_, v___x_1861_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_m_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_1868_, lean_object* v_k_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v_m_1874_; lean_object* v_a_1875_; uint8_t v___x_1876_; 
v___x_1872_ = lean_nat_add(v_x_1870_, v_x_1871_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v_m_1874_ = lean_nat_shiftr(v___x_1872_, v___x_1873_);
lean_dec(v___x_1872_);
v_a_1875_ = lean_array_fget_borrowed(v_as_1868_, v_m_1874_);
v___x_1876_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_1875_, v_k_1869_);
if (v___x_1876_ == 0)
{
uint8_t v___x_1877_; 
lean_dec(v_x_1871_);
v___x_1877_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_1869_, v_a_1875_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
lean_dec(v_m_1874_);
lean_dec(v_x_1870_);
lean_inc(v_a_1875_);
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_a_1875_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_nat_dec_eq(v_m_1874_, v___x_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = lean_nat_sub(v_m_1874_, v___x_1873_);
lean_dec(v_m_1874_);
v___x_1882_ = lean_nat_dec_lt(v___x_1881_, v_x_1870_);
if (v___x_1882_ == 0)
{
v_x_1871_ = v___x_1881_;
goto _start;
}
else
{
lean_object* v___x_1884_; 
lean_dec(v___x_1881_);
lean_dec(v_x_1870_);
v___x_1884_ = lean_box(0);
return v___x_1884_;
}
}
else
{
lean_object* v___x_1885_; 
lean_dec(v_m_1874_);
lean_dec(v_x_1870_);
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
}
}
else
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
lean_dec(v_x_1870_);
v___x_1886_ = lean_nat_add(v_m_1874_, v___x_1873_);
lean_dec(v_m_1874_);
v___x_1887_ = lean_nat_dec_le(v___x_1886_, v_x_1871_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_dec(v___x_1886_);
lean_dec(v_x_1871_);
v___x_1888_ = lean_box(0);
return v___x_1888_;
}
else
{
v_x_1870_ = v___x_1886_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_1890_, lean_object* v_k_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_1890_, v_k_1891_, v_x_1892_, v_x_1893_);
lean_dec_ref(v_k_1891_);
lean_dec_ref(v_as_1890_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_i_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_get_size(v_keys_1895_);
v___x_1900_ = lean_nat_dec_lt(v_i_1897_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; 
lean_dec(v_i_1897_);
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
else
{
lean_object* v_k_x27_1902_; uint8_t v___x_1903_; 
v_k_x27_1902_ = lean_array_fget_borrowed(v_keys_1895_, v_i_1897_);
v___x_1903_ = lean_name_eq(v_k_1898_, v_k_x27_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_i_1897_, v___x_1904_);
lean_dec(v_i_1897_);
v_i_1897_ = v___x_1905_;
goto _start;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_array_fget_borrowed(v_vals_1896_, v_i_1897_);
lean_dec(v_i_1897_);
lean_inc(v___x_1907_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_1909_, lean_object* v_vals_1910_, lean_object* v_i_1911_, lean_object* v_k_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_1909_, v_vals_1910_, v_i_1911_, v_k_1912_);
lean_dec(v_k_1912_);
lean_dec_ref(v_vals_1910_);
lean_dec_ref(v_keys_1909_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object* v_x_1914_, size_t v_x_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_object* v_es_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1938_; 
v_es_1917_ = lean_ctor_get(v_x_1914_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1914_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1919_ = v_x_1914_;
v_isShared_1920_ = v_isSharedCheck_1938_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_es_1917_);
lean_dec(v_x_1914_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1938_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; size_t v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; lean_object* v_j_1925_; lean_object* v___x_1926_; 
v___x_1921_ = lean_box(2);
v___x_1922_ = ((size_t)5ULL);
v___x_1923_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_1924_ = lean_usize_land(v_x_1915_, v___x_1923_);
v_j_1925_ = lean_usize_to_nat(v___x_1924_);
v___x_1926_ = lean_array_get(v___x_1921_, v_es_1917_, v_j_1925_);
lean_dec(v_j_1925_);
lean_dec_ref(v_es_1917_);
switch(lean_obj_tag(v___x_1926_))
{
case 0:
{
lean_object* v_key_1927_; lean_object* v_val_1928_; uint8_t v___x_1929_; 
v_key_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_key_1927_);
v_val_1928_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_val_1928_);
lean_dec_ref(v___x_1926_);
v___x_1929_ = lean_name_eq(v_x_1916_, v_key_1927_);
lean_dec(v_key_1927_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec(v_val_1928_);
lean_del_object(v___x_1919_);
v___x_1930_ = lean_box(0);
return v___x_1930_;
}
else
{
lean_object* v___x_1932_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 1);
lean_ctor_set(v___x_1919_, 0, v_val_1928_);
v___x_1932_ = v___x_1919_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_val_1928_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
case 1:
{
lean_object* v_node_1934_; size_t v___x_1935_; 
lean_del_object(v___x_1919_);
v_node_1934_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_node_1934_);
lean_dec_ref(v___x_1926_);
v___x_1935_ = lean_usize_shift_right(v_x_1915_, v___x_1922_);
v_x_1914_ = v_node_1934_;
v_x_1915_ = v___x_1935_;
goto _start;
}
default: 
{
lean_object* v___x_1937_; 
lean_del_object(v___x_1919_);
v___x_1937_ = lean_box(0);
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_ks_1939_; lean_object* v_vs_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_ks_1939_ = lean_ctor_get(v_x_1914_, 0);
lean_inc_ref(v_ks_1939_);
v_vs_1940_ = lean_ctor_get(v_x_1914_, 1);
lean_inc_ref(v_vs_1940_);
lean_dec_ref(v_x_1914_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_1939_, v_vs_1940_, v___x_1941_, v_x_1916_);
lean_dec_ref(v_vs_1940_);
lean_dec_ref(v_ks_1939_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
size_t v_x_1442__boxed_1946_; lean_object* v_res_1947_; 
v_x_1442__boxed_1946_ = lean_unbox_usize(v_x_1944_);
lean_dec(v_x_1944_);
v_res_1947_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_1943_, v_x_1442__boxed_1946_, v_x_1945_);
lean_dec(v_x_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_1948_, lean_object* v_x_1949_){
_start:
{
uint64_t v___y_1951_; 
if (lean_obj_tag(v_x_1949_) == 0)
{
uint64_t v___x_1954_; 
v___x_1954_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1951_ = v___x_1954_;
goto v___jp_1950_;
}
else
{
uint64_t v_hash_1955_; 
v_hash_1955_ = lean_ctor_get_uint64(v_x_1949_, sizeof(void*)*2);
v___y_1951_ = v_hash_1955_;
goto v___jp_1950_;
}
v___jp_1950_:
{
size_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_uint64_to_usize(v___y_1951_);
v___x_1953_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_1948_, v___x_1952_, v_x_1949_);
return v___x_1953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_1956_, v_x_1957_);
lean_dec(v_x_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object* v_declName_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v_env_1963_; lean_object* v___x_1964_; lean_object* v___x_1974_; 
v___x_1962_ = lean_st_ref_get(v_a_1960_);
v_env_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc_ref(v_env_1963_);
lean_dec(v___x_1962_);
v___x_1964_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_1974_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1963_, v_declName_1959_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; lean_object* v_toEnvExtension_1976_; lean_object* v_asyncMode_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_newEntries_1980_; lean_object* v___x_1981_; 
v___x_1975_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_1976_ = lean_ctor_get(v___x_1975_, 0);
v_asyncMode_1977_ = lean_ctor_get(v_toEnvExtension_1976_, 2);
v___x_1978_ = lean_box(0);
lean_inc_ref(v_env_1963_);
v___x_1979_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1964_, v___x_1975_, v_env_1963_, v_asyncMode_1977_, v___x_1978_);
v_newEntries_1980_ = lean_ctor_get(v___x_1979_, 1);
lean_inc_ref(v_newEntries_1980_);
lean_dec(v___x_1979_);
v___x_1981_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_1980_, v_declName_1959_);
if (lean_obj_tag(v___x_1981_) == 1)
{
lean_object* v___x_1982_; 
lean_dec_ref(v_env_1963_);
lean_dec(v_declName_1959_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
else
{
lean_dec(v___x_1981_);
goto v___jp_1965_;
}
}
else
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2011_; 
v_val_1983_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_2011_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2011_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1987_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v___x_1988_ = 0;
v___x_1989_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1964_, v___x_1987_, v_env_1963_, v_val_1983_, v___x_1988_);
lean_dec(v_val_1983_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_array_get_size(v___x_1989_);
v___x_1992_ = lean_nat_dec_lt(v___x_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_dec_ref(v___x_1989_);
lean_del_object(v___x_1985_);
goto v___jp_1965_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_nat_sub(v___x_1991_, v___x_1993_);
v___x_1995_ = lean_nat_dec_le(v___x_1990_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec(v___x_1994_);
lean_dec_ref(v___x_1989_);
lean_del_object(v___x_1985_);
goto v___jp_1965_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0));
lean_inc(v_declName_1959_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_declName_1959_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_1989_, v___x_1997_, v___x_1990_, v___x_1994_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_env_1963_);
lean_dec(v_declName_1959_);
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2010_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2010_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_keys_2003_; lean_object* v___x_2005_; 
v_keys_2003_ = lean_ctor_get(v_val_1999_, 1);
lean_inc_ref(v_keys_2003_);
lean_dec(v_val_1999_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_keys_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_keys_2003_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 0);
lean_ctor_set(v___x_1985_, 0, v___x_2005_);
v___x_2007_ = v___x_1985_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_dec(v___x_1998_);
lean_del_object(v___x_1985_);
goto v___jp_1965_;
}
}
}
}
}
v___jp_1965_:
{
lean_object* v___x_1966_; lean_object* v_toEnvExtension_1967_; lean_object* v_asyncMode_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v_builtin_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1966_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_1967_ = lean_ctor_get(v___x_1966_, 0);
v_asyncMode_1968_ = lean_ctor_get(v_toEnvExtension_1967_, 2);
v___x_1969_ = lean_box(0);
v___x_1970_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1964_, v___x_1966_, v_env_1963_, v_asyncMode_1968_, v___x_1969_);
v_builtin_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc_ref(v_builtin_1971_);
lean_dec(v___x_1970_);
v___x_1972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_1971_, v_declName_1959_);
lean_dec(v_declName_1959_);
lean_dec_ref(v_builtin_1971_);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2012_, v_a_2013_);
lean_dec(v_a_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object* v_declName_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2016_, v_a_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object* v_declName_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2021_, v_a_2022_, v_a_2023_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_2026_, lean_object* v_m_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2027_, v_a_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_2030_, lean_object* v_m_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_2030_, v_m_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec_ref(v_m_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_2038_, v_x_2039_, v_x_2040_);
lean_dec(v_x_2040_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object* v_as_2042_, lean_object* v_k_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2042_, v_k_2043_, v_x_2044_, v_x_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_2048_, lean_object* v_k_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(v_as_2048_, v_k_2049_, v_x_2050_, v_x_2051_, v_x_2052_);
lean_dec_ref(v_k_2049_);
lean_dec_ref(v_as_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2054_, lean_object* v_a_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2055_, v_x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2058_, lean_object* v_a_2059_, lean_object* v_x_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_2058_, v_a_2059_, v_x_2060_);
lean_dec(v_x_2060_);
lean_dec(v_a_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2062_, lean_object* v_x_2063_, size_t v_x_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2063_, v_x_2064_, v_x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
size_t v_x_1643__boxed_2071_; lean_object* v_res_2072_; 
v_x_1643__boxed_2071_ = lean_unbox_usize(v_x_2069_);
lean_dec(v_x_2069_);
v_res_2072_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_2067_, v_x_2068_, v_x_1643__boxed_2071_, v_x_2070_);
lean_dec(v_x_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2073_, lean_object* v_keys_2074_, lean_object* v_vals_2075_, lean_object* v_heq_2076_, lean_object* v_i_2077_, lean_object* v_k_2078_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2074_, v_vals_2075_, v_i_2077_, v_k_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2080_, lean_object* v_keys_2081_, lean_object* v_vals_2082_, lean_object* v_heq_2083_, lean_object* v_i_2084_, lean_object* v_k_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_2080_, v_keys_2081_, v_vals_2082_, v_heq_2083_, v_i_2084_, v_k_2085_);
lean_dec(v_k_2085_);
lean_dec_ref(v_vals_2082_);
lean_dec_ref(v_keys_2081_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object* v_declName_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2105_; 
v___x_2090_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2087_, v_a_2088_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
if (lean_obj_tag(v_a_2091_) == 0)
{
uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2095_ = 0;
v___x_2096_ = lean_box(v___x_2095_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
else
{
uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_dec_ref(v_a_2091_);
v___x_2100_ = 1;
v___x_2101_ = lean_box(v___x_2100_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2101_);
v___x_2103_ = v___x_2093_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object* v_declName_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2106_, v_a_2107_);
lean_dec(v_a_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object* v_declName_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2110_, v_a_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object* v_declName_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object* v_declName_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v_env_2124_; lean_object* v___x_2125_; lean_object* v_toEnvExtension_2126_; lean_object* v_asyncMode_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v_builtin_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2123_ = lean_st_ref_get(v_a_2121_);
v_env_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_ref(v_env_2124_);
lean_dec(v___x_2123_);
v___x_2125_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2126_ = lean_ctor_get(v___x_2125_, 0);
v_asyncMode_2127_ = lean_ctor_get(v_toEnvExtension_2126_, 2);
v___x_2128_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2129_ = lean_box(0);
v___x_2130_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2128_, v___x_2125_, v_env_2124_, v_asyncMode_2127_, v___x_2129_);
v_builtin_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_ref(v_builtin_2131_);
lean_dec(v___x_2130_);
v___x_2132_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_2131_, v_declName_2120_);
lean_dec_ref(v_builtin_2131_);
v___x_2133_ = lean_box(v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object* v_declName_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec(v_declName_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object* v_declName_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2139_, v_a_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object* v_declName_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_declName_2144_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object* v_declName_2149_, lean_object* v_keys_2150_, lean_object* v_s_2151_){
_start:
{
lean_object* v_builtin_2152_; lean_object* v_newEntries_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
v_builtin_2152_ = lean_ctor_get(v_s_2151_, 0);
v_newEntries_2153_ = lean_ctor_get(v_s_2151_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_s_2151_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v_s_2151_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_newEntries_2153_);
lean_inc(v_builtin_2152_);
lean_dec(v_s_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_2153_, v_declName_2149_, v_keys_2150_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_builtin_2152_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
lean_ctor_set(v___x_2167_, 2, v___x_2166_);
lean_ctor_set(v___x_2167_, 3, v___x_2166_);
lean_ctor_set(v___x_2167_, 4, v___x_2165_);
lean_ctor_set(v___x_2167_, 5, v___x_2165_);
lean_ctor_set(v___x_2167_, 6, v___x_2165_);
lean_ctor_set(v___x_2167_, 7, v___x_2165_);
lean_ctor_set(v___x_2167_, 8, v___x_2165_);
lean_ctor_set(v___x_2167_, 9, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_unsigned_to_nat(32u);
v___x_2169_ = lean_mk_empty_array_with_capacity(v___x_2168_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2171_ = ((size_t)5ULL);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = lean_unsigned_to_nat(32u);
v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
v___x_2175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
v___x_2176_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2174_);
lean_ctor_set(v___x_2176_, 2, v___x_2172_);
lean_ctor_set(v___x_2176_, 3, v___x_2172_);
lean_ctor_set_usize(v___x_2176_, 4, v___x_2171_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = lean_box(1);
v___x_2178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
v___x_2179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2178_);
lean_ctor_set(v___x_2180_, 2, v___x_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object* v_msgData_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; lean_object* v_env_2186_; lean_object* v_options_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2185_ = lean_st_ref_get(v___y_2183_);
v_env_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc_ref(v_env_2186_);
lean_dec(v___x_2185_);
v_options_2187_ = lean_ctor_get(v___y_2182_, 2);
v___x_2188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2187_);
v___x_2190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2190_, 0, v_env_2186_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_ctor_set(v___x_2190_, 3, v_options_2187_);
v___x_2191_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_msgData_2181_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object* v_msg_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_ref_2202_; lean_object* v___x_2203_; lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
v_ref_2202_ = lean_ctor_get(v___y_2199_, 5);
v___x_2203_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_2198_, v___y_2199_, v___y_2200_);
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
lean_inc(v_ref_2202_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_ref_2202_);
lean_ctor_set(v___x_2208_, 1, v_a_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set_tag(v___x_2206_, 1);
lean_ctor_set(v___x_2206_, 0, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object* v_msg_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2217_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0(void){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object* v_declName_2231_, lean_object* v_keys_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___x_2236_; lean_object* v_env_2237_; lean_object* v___f_2238_; lean_object* v___y_2240_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___x_2288_; 
v___x_2236_ = lean_st_ref_get(v_a_2234_);
v_env_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc_ref(v_env_2237_);
lean_dec(v___x_2236_);
lean_inc(v_declName_2231_);
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0), 3, 2);
lean_closure_set(v___f_2238_, 0, v_declName_2231_);
lean_closure_set(v___f_2238_, 1, v_keys_2232_);
v___x_2288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2237_, v_declName_2231_);
lean_dec_ref(v_env_2237_);
if (lean_obj_tag(v___x_2288_) == 0)
{
v___y_2268_ = v_a_2233_;
v___y_2269_ = v_a_2234_;
goto v___jp_2267_;
}
else
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___f_2238_);
v___x_2289_ = 0;
v___x_2290_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2291_ = l_Lean_MessageData_ofConstName(v_declName_2231_, v___x_2289_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2294_, v_a_2233_, v_a_2234_);
return v___x_2295_;
}
v___jp_2239_:
{
lean_object* v___x_2241_; lean_object* v_env_2242_; lean_object* v_nextMacroScope_2243_; lean_object* v_ngen_2244_; lean_object* v_auxDeclNGen_2245_; lean_object* v_traceState_2246_; lean_object* v_messages_2247_; lean_object* v_infoState_2248_; lean_object* v_snapshotTasks_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2265_; 
v___x_2241_ = lean_st_ref_take(v___y_2240_);
v_env_2242_ = lean_ctor_get(v___x_2241_, 0);
v_nextMacroScope_2243_ = lean_ctor_get(v___x_2241_, 1);
v_ngen_2244_ = lean_ctor_get(v___x_2241_, 2);
v_auxDeclNGen_2245_ = lean_ctor_get(v___x_2241_, 3);
v_traceState_2246_ = lean_ctor_get(v___x_2241_, 4);
v_messages_2247_ = lean_ctor_get(v___x_2241_, 6);
v_infoState_2248_ = lean_ctor_get(v___x_2241_, 7);
v_snapshotTasks_2249_ = lean_ctor_get(v___x_2241_, 8);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2265_ == 0)
{
lean_object* v_unused_2266_; 
v_unused_2266_ = lean_ctor_get(v___x_2241_, 5);
lean_dec(v_unused_2266_);
v___x_2251_ = v___x_2241_;
v_isShared_2252_ = v_isSharedCheck_2265_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_snapshotTasks_2249_);
lean_inc(v_infoState_2248_);
lean_inc(v_messages_2247_);
lean_inc(v_traceState_2246_);
lean_inc(v_auxDeclNGen_2245_);
lean_inc(v_ngen_2244_);
lean_inc(v_nextMacroScope_2243_);
lean_inc(v_env_2242_);
lean_dec(v___x_2241_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2265_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v_toEnvExtension_2254_; lean_object* v_asyncMode_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2253_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2254_ = lean_ctor_get(v___x_2253_, 0);
v_asyncMode_2255_ = lean_ctor_get(v_toEnvExtension_2254_, 2);
v___x_2256_ = lean_box(0);
v___x_2257_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2253_, v_env_2242_, v___f_2238_, v_asyncMode_2255_, v___x_2256_);
v___x_2258_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 5, v___x_2258_);
lean_ctor_set(v___x_2251_, 0, v___x_2257_);
v___x_2260_ = v___x_2251_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_nextMacroScope_2243_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_ngen_2244_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_auxDeclNGen_2245_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v_traceState_2246_);
lean_ctor_set(v_reuseFailAlloc_2264_, 5, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2264_, 6, v_messages_2247_);
lean_ctor_set(v_reuseFailAlloc_2264_, 7, v_infoState_2248_);
lean_ctor_set(v_reuseFailAlloc_2264_, 8, v_snapshotTasks_2249_);
v___x_2260_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_st_ref_set(v___y_2240_, v___x_2260_);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
}
}
v___jp_2267_:
{
lean_object* v___x_2270_; 
lean_inc(v_declName_2231_);
v___x_2270_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2231_, v___y_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; uint8_t v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v_declName_2231_);
v___y_2240_ = v___y_2269_;
goto v___jp_2239_;
}
else
{
lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v___f_2238_);
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2274_ = 0;
v___x_2275_ = l_Lean_MessageData_ofConstName(v_declName_2231_, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2278_, v___y_2268_, v___y_2269_);
return v___x_2279_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v___f_2238_);
lean_dec(v_declName_2231_);
v_a_2280_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2270_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2270_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object* v_declName_2296_, lean_object* v_keys_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2296_, v_keys_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object* v_00_u03b1_2302_, lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(v_00_u03b1_2308_, v_msg_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_2314_){
_start:
{
if (lean_obj_tag(v_e_2314_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
v_a_2316_ = lean_ctor_get(v_e_2314_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_e_2314_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v_e_2314_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v_e_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2320_ = lean_mk_io_user_error(v_a_2316_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 1);
lean_ctor_set(v___x_2318_, 0, v___x_2320_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
v_a_2325_ = lean_ctor_get(v_e_2314_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_e_2314_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v_e_2314_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v_e_2314_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set_tag(v___x_2327_, 0);
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_2336_, lean_object* v_e_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_2340_, lean_object* v_e_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(v_00_u03b1_2340_, v_e_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object* v_declName_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_env_2354_; lean_object* v_opts_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; 
v_env_2354_ = lean_ctor_get(v_a_2352_, 0);
v_opts_2355_ = lean_ctor_get(v_a_2352_, 1);
v___x_2356_ = 0;
lean_inc(v_declName_2351_);
lean_inc_ref(v_env_2354_);
v___x_2357_ = l_Lean_Environment_find_x3f(v_env_2354_, v_declName_2351_, v___x_2356_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2358_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0));
v___x_2359_ = 1;
v___x_2360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2351_, v___x_2359_);
v___x_2361_ = lean_string_append(v___x_2358_, v___x_2360_);
lean_dec_ref(v___x_2360_);
v___x_2362_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2363_ = lean_string_append(v___x_2361_, v___x_2362_);
v___x_2364_ = lean_mk_io_user_error(v___x_2363_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
else
{
lean_object* v_val_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2411_; 
v_val_2366_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2368_ = v___x_2357_;
v_isShared_2369_ = v_isSharedCheck_2411_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_val_2366_);
lean_dec(v___x_2357_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2411_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_ConstantInfo_type(v_val_2366_);
if (lean_obj_tag(v___x_2387_) == 4)
{
lean_object* v_declName_2388_; 
v_declName_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_declName_2388_);
lean_dec_ref(v___x_2387_);
if (lean_obj_tag(v_declName_2388_) == 1)
{
lean_object* v_pre_2389_; 
v_pre_2389_ = lean_ctor_get(v_declName_2388_, 0);
lean_inc(v_pre_2389_);
if (lean_obj_tag(v_pre_2389_) == 1)
{
lean_object* v_pre_2390_; 
v_pre_2390_ = lean_ctor_get(v_pre_2389_, 0);
lean_inc(v_pre_2390_);
if (lean_obj_tag(v_pre_2390_) == 1)
{
lean_object* v_pre_2391_; 
v_pre_2391_ = lean_ctor_get(v_pre_2390_, 0);
lean_inc(v_pre_2391_);
if (lean_obj_tag(v_pre_2391_) == 1)
{
lean_object* v_pre_2392_; 
v_pre_2392_ = lean_ctor_get(v_pre_2391_, 0);
lean_inc(v_pre_2392_);
if (lean_obj_tag(v_pre_2392_) == 1)
{
lean_object* v_pre_2393_; 
v_pre_2393_ = lean_ctor_get(v_pre_2392_, 0);
if (lean_obj_tag(v_pre_2393_) == 0)
{
lean_object* v_str_2394_; lean_object* v_str_2395_; lean_object* v_str_2396_; lean_object* v_str_2397_; lean_object* v_str_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v_str_2394_ = lean_ctor_get(v_declName_2388_, 1);
lean_inc_ref(v_str_2394_);
lean_dec_ref(v_declName_2388_);
v_str_2395_ = lean_ctor_get(v_pre_2389_, 1);
lean_inc_ref(v_str_2395_);
lean_dec_ref(v_pre_2389_);
v_str_2396_ = lean_ctor_get(v_pre_2390_, 1);
lean_inc_ref(v_str_2396_);
lean_dec_ref(v_pre_2390_);
v_str_2397_ = lean_ctor_get(v_pre_2391_, 1);
lean_inc_ref(v_str_2397_);
lean_dec_ref(v_pre_2391_);
v_str_2398_ = lean_ctor_get(v_pre_2392_, 1);
lean_inc_ref(v_str_2398_);
lean_dec_ref(v_pre_2392_);
v___x_2399_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0));
v___x_2400_ = lean_string_dec_eq(v_str_2398_, v___x_2399_);
lean_dec_ref(v_str_2398_);
if (v___x_2400_ == 0)
{
lean_dec_ref(v_str_2397_);
lean_dec_ref(v_str_2396_);
lean_dec_ref(v_str_2395_);
lean_dec_ref(v_str_2394_);
goto v___jp_2370_;
}
else
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1));
v___x_2402_ = lean_string_dec_eq(v_str_2397_, v___x_2401_);
lean_dec_ref(v_str_2397_);
if (v___x_2402_ == 0)
{
lean_dec_ref(v_str_2396_);
lean_dec_ref(v_str_2395_);
lean_dec_ref(v_str_2394_);
goto v___jp_2370_;
}
else
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4));
v___x_2404_ = lean_string_dec_eq(v_str_2396_, v___x_2403_);
lean_dec_ref(v_str_2396_);
if (v___x_2404_ == 0)
{
lean_dec_ref(v_str_2395_);
lean_dec_ref(v_str_2394_);
goto v___jp_2370_;
}
else
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5));
v___x_2406_ = lean_string_dec_eq(v_str_2395_, v___x_2405_);
lean_dec_ref(v_str_2395_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v_str_2394_);
goto v___jp_2370_;
}
else
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6));
v___x_2408_ = lean_string_dec_eq(v_str_2394_, v___x_2407_);
lean_dec_ref(v_str_2394_);
if (v___x_2408_ == 0)
{
goto v___jp_2370_;
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
v___x_2409_ = l_Lean_Environment_evalConst___redArg(v_env_2354_, v_opts_2355_, v_declName_2351_, v___x_2408_);
lean_dec(v_declName_2351_);
v___x_2410_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_2409_);
return v___x_2410_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2392_);
lean_dec_ref(v_pre_2391_);
lean_dec_ref(v_pre_2390_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_declName_2388_);
goto v___jp_2370_;
}
}
else
{
lean_dec_ref(v_pre_2391_);
lean_dec(v_pre_2392_);
lean_dec_ref(v_pre_2390_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_declName_2388_);
goto v___jp_2370_;
}
}
else
{
lean_dec_ref(v_pre_2390_);
lean_dec(v_pre_2391_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_declName_2388_);
goto v___jp_2370_;
}
}
else
{
lean_dec(v_pre_2390_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_declName_2388_);
goto v___jp_2370_;
}
}
else
{
lean_dec_ref(v_declName_2388_);
lean_dec(v_pre_2389_);
goto v___jp_2370_;
}
}
else
{
lean_dec(v_declName_2388_);
goto v___jp_2370_;
}
}
else
{
lean_dec_ref(v___x_2387_);
goto v___jp_2370_;
}
v___jp_2370_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2371_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2));
v___x_2372_ = l_Lean_privateToUserName(v_declName_2351_);
v___x_2373_ = 1;
v___x_2374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_string_append(v___x_2371_, v___x_2374_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3));
v___x_2377_ = lean_string_append(v___x_2375_, v___x_2376_);
v___x_2378_ = l_Lean_ConstantInfo_type(v_val_2366_);
lean_dec(v_val_2366_);
v___x_2379_ = lean_expr_dbg_to_string(v___x_2378_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_string_append(v___x_2377_, v___x_2379_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2382_ = lean_string_append(v___x_2380_, v___x_2381_);
v___x_2383_ = lean_mk_io_user_error(v___x_2382_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2383_);
v___x_2385_ = v___x_2368_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object* v_declName_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2412_, v_a_2413_);
lean_dec_ref(v_a_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object* v_e_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_declName_2419_; lean_object* v___x_2420_; 
v_declName_2419_ = lean_ctor_get(v_e_2416_, 0);
lean_inc(v_declName_2419_);
v___x_2420_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2419_, v_a_2417_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_e_2416_);
lean_ctor_set(v___x_2425_, 1, v_a_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v_e_2416_);
v_a_2430_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2420_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2420_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object* v_e_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2438_, v_a_2439_);
lean_dec_ref(v_a_2439_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
v___x_2444_ = lean_st_mk_ref(v___x_2443_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___y_2448_){
_start:
{
lean_inc_ref(v___y_2448_);
return v___y_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_2449_);
lean_dec_ref(v___y_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_2452_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2456_, v___y_2457_, v___y_2458_);
lean_dec_ref(v___y_2458_);
lean_dec_ref(v_x_2456_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_e_2461_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2462_; 
v_toCbvSimprocOLeanEntry_2462_ = lean_ctor_get(v_e_2461_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2462_);
return v_toCbvSimprocOLeanEntry_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_e_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_2463_);
lean_dec_ref(v_e_2463_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_s_2465_, lean_object* v_e_2466_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2467_; lean_object* v_proc_2468_; lean_object* v_declName_2469_; uint8_t v_phase_2470_; lean_object* v_keys_2471_; lean_object* v___x_2472_; 
v_toCbvSimprocOLeanEntry_2467_ = lean_ctor_get(v_e_2466_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2467_);
v_proc_2468_ = lean_ctor_get(v_e_2466_, 1);
lean_inc_ref(v_proc_2468_);
lean_dec_ref(v_e_2466_);
v_declName_2469_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2467_, 0);
lean_inc(v_declName_2469_);
v_phase_2470_ = lean_ctor_get_uint8(v_toCbvSimprocOLeanEntry_2467_, sizeof(void*)*2);
v_keys_2471_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2467_, 1);
lean_inc_ref(v_keys_2471_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_2467_);
v___x_2472_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_2465_, v_keys_2471_, v_declName_2469_, v_phase_2470_, v_proc_2468_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(uint8_t v_x_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___y_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2476_, lean_object* v___y_2477_){
_start:
{
uint8_t v_x_126__boxed_2478_; lean_object* v_res_2479_; 
v_x_126__boxed_2478_ = lean_unbox(v_x_2476_);
v_res_2479_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_126__boxed_2478_, v___y_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___x_2480_){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_st_ref_get(v___x_2480_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___x_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2484_);
lean_dec(v___x_2484_);
return v_res_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___f_2496_; 
v___x_2495_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___f_2496_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2496_, 0, v___x_2495_);
return v___f_2496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2497_; lean_object* v___f_2498_; lean_object* v___f_2499_; lean_object* v___f_2500_; lean_object* v___f_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___f_2497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___x_2504_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___f_2502_);
lean_ctor_set(v___x_2504_, 2, v___f_2501_);
lean_ctor_set(v___x_2504_, 3, v___f_2500_);
lean_ctor_set(v___x_2504_, 4, v___f_2499_);
lean_ctor_set(v___x_2504_, 5, v___f_2498_);
lean_ctor_set(v___x_2504_, 6, v___f_2497_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2507_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object* v_declName_2510_, lean_object* v_s_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_2511_, v_declName_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2513_, lean_object* v_i_2514_, lean_object* v_k_2515_){
_start:
{
lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2516_ = lean_array_get_size(v_keys_2513_);
v___x_2517_ = lean_nat_dec_lt(v_i_2514_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_dec(v_i_2514_);
return v___x_2517_;
}
else
{
lean_object* v_k_x27_2518_; uint8_t v___x_2519_; 
v_k_x27_2518_ = lean_array_fget_borrowed(v_keys_2513_, v_i_2514_);
v___x_2519_ = lean_name_eq(v_k_2515_, v_k_x27_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = lean_nat_add(v_i_2514_, v___x_2520_);
lean_dec(v_i_2514_);
v_i_2514_ = v___x_2521_;
goto _start;
}
else
{
lean_dec(v_i_2514_);
return v___x_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2523_, lean_object* v_i_2524_, lean_object* v_k_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2523_, v_i_2524_, v_k_2525_);
lean_dec(v_k_2525_);
lean_dec_ref(v_keys_2523_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_2528_, size_t v_x_2529_, lean_object* v_x_2530_){
_start:
{
if (lean_obj_tag(v_x_2528_) == 0)
{
lean_object* v_es_2531_; lean_object* v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v_j_2536_; lean_object* v___x_2537_; 
v_es_2531_ = lean_ctor_get(v_x_2528_, 0);
v___x_2532_ = lean_box(2);
v___x_2533_ = ((size_t)5ULL);
v___x_2534_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_2535_ = lean_usize_land(v_x_2529_, v___x_2534_);
v_j_2536_ = lean_usize_to_nat(v___x_2535_);
v___x_2537_ = lean_array_get_borrowed(v___x_2532_, v_es_2531_, v_j_2536_);
lean_dec(v_j_2536_);
switch(lean_obj_tag(v___x_2537_))
{
case 0:
{
lean_object* v_key_2538_; uint8_t v___x_2539_; 
v_key_2538_ = lean_ctor_get(v___x_2537_, 0);
v___x_2539_ = lean_name_eq(v_x_2530_, v_key_2538_);
return v___x_2539_;
}
case 1:
{
lean_object* v_node_2540_; size_t v___x_2541_; 
v_node_2540_ = lean_ctor_get(v___x_2537_, 0);
v___x_2541_ = lean_usize_shift_right(v_x_2529_, v___x_2533_);
v_x_2528_ = v_node_2540_;
v_x_2529_ = v___x_2541_;
goto _start;
}
default: 
{
uint8_t v___x_2543_; 
v___x_2543_ = 0;
return v___x_2543_;
}
}
}
else
{
lean_object* v_ks_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v_ks_2544_ = lean_ctor_get(v_x_2528_, 0);
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_2544_, v___x_2545_, v_x_2530_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_){
_start:
{
size_t v_x_556__boxed_2550_; uint8_t v_res_2551_; lean_object* v_r_2552_; 
v_x_556__boxed_2550_ = lean_unbox_usize(v_x_2548_);
lean_dec(v_x_2548_);
v_res_2551_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2547_, v_x_556__boxed_2550_, v_x_2549_);
lean_dec(v_x_2549_);
lean_dec_ref(v_x_2547_);
v_r_2552_ = lean_box(v_res_2551_);
return v_r_2552_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object* v_x_2553_, lean_object* v_x_2554_){
_start:
{
uint64_t v___y_2556_; 
if (lean_obj_tag(v_x_2554_) == 0)
{
uint64_t v___x_2559_; 
v___x_2559_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2556_ = v___x_2559_;
goto v___jp_2555_;
}
else
{
uint64_t v_hash_2560_; 
v_hash_2560_ = lean_ctor_get_uint64(v_x_2554_, sizeof(void*)*2);
v___y_2556_ = v_hash_2560_;
goto v___jp_2555_;
}
v___jp_2555_:
{
size_t v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = lean_uint64_to_usize(v___y_2556_);
v___x_2558_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2553_, v___x_2557_, v_x_2554_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_2561_, lean_object* v_x_2562_){
_start:
{
uint8_t v_res_2563_; lean_object* v_r_2564_; 
v_res_2563_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2561_, v_x_2562_);
lean_dec(v_x_2562_);
lean_dec_ref(v_x_2561_);
v_r_2564_ = lean_box(v_res_2563_);
return v_r_2564_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2566_ = l_Lean_stringToMessageData(v___x_2565_);
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1));
v___x_2569_ = l_Lean_stringToMessageData(v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object* v_declName_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; lean_object* v_env_2575_; lean_object* v___x_2576_; lean_object* v_ext_2577_; lean_object* v_toEnvExtension_2578_; lean_object* v_asyncMode_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_simprocNames_2582_; lean_object* v___f_2583_; lean_object* v___y_2585_; uint8_t v___x_2608_; 
v___x_2574_ = lean_st_ref_get(v_a_2572_);
v_env_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc_ref(v_env_2575_);
lean_dec(v___x_2574_);
v___x_2576_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_2577_ = lean_ctor_get(v___x_2576_, 1);
v_toEnvExtension_2578_ = lean_ctor_get(v_ext_2577_, 0);
v_asyncMode_2579_ = lean_ctor_get(v_toEnvExtension_2578_, 2);
v___x_2580_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_2581_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2580_, v___x_2576_, v_env_2575_, v_asyncMode_2579_);
v_simprocNames_2582_ = lean_ctor_get(v___x_2581_, 3);
lean_inc_ref(v_simprocNames_2582_);
lean_dec(v___x_2581_);
lean_inc(v_declName_2570_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_2583_, 0, v_declName_2570_);
v___x_2608_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_2582_, v_declName_2570_);
lean_dec_ref(v_simprocNames_2582_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref(v___f_2583_);
v___x_2609_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0);
v___x_2610_ = l_Lean_MessageData_ofConstName(v_declName_2570_, v___x_2608_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2613_, v_a_2571_, v_a_2572_);
return v___x_2614_;
}
else
{
lean_dec(v_declName_2570_);
v___y_2585_ = v_a_2572_;
goto v___jp_2584_;
}
v___jp_2584_:
{
lean_object* v___x_2586_; lean_object* v_env_2587_; lean_object* v_nextMacroScope_2588_; lean_object* v_ngen_2589_; lean_object* v_auxDeclNGen_2590_; lean_object* v_traceState_2591_; lean_object* v_messages_2592_; lean_object* v_infoState_2593_; lean_object* v_snapshotTasks_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2606_; 
v___x_2586_ = lean_st_ref_take(v___y_2585_);
v_env_2587_ = lean_ctor_get(v___x_2586_, 0);
v_nextMacroScope_2588_ = lean_ctor_get(v___x_2586_, 1);
v_ngen_2589_ = lean_ctor_get(v___x_2586_, 2);
v_auxDeclNGen_2590_ = lean_ctor_get(v___x_2586_, 3);
v_traceState_2591_ = lean_ctor_get(v___x_2586_, 4);
v_messages_2592_ = lean_ctor_get(v___x_2586_, 6);
v_infoState_2593_ = lean_ctor_get(v___x_2586_, 7);
v_snapshotTasks_2594_ = lean_ctor_get(v___x_2586_, 8);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v___x_2586_, 5);
lean_dec(v_unused_2607_);
v___x_2596_ = v___x_2586_;
v_isShared_2597_ = v_isSharedCheck_2606_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_snapshotTasks_2594_);
lean_inc(v_infoState_2593_);
lean_inc(v_messages_2592_);
lean_inc(v_traceState_2591_);
lean_inc(v_auxDeclNGen_2590_);
lean_inc(v_ngen_2589_);
lean_inc(v_nextMacroScope_2588_);
lean_inc(v_env_2587_);
lean_dec(v___x_2586_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2606_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2598_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2576_, v_env_2587_, v___f_2583_);
v___x_2599_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 5, v___x_2599_);
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2601_ = v___x_2596_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_nextMacroScope_2588_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_ngen_2589_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_auxDeclNGen_2590_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_traceState_2591_);
lean_ctor_set(v_reuseFailAlloc_2605_, 5, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2605_, 6, v_messages_2592_);
lean_ctor_set(v_reuseFailAlloc_2605_, 7, v_infoState_2593_);
lean_ctor_set(v_reuseFailAlloc_2605_, 8, v_snapshotTasks_2594_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_st_ref_set(v___y_2585_, v___x_2601_);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object* v_declName_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
return v_res_2619_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2621_, v_x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
uint8_t v_res_2627_; lean_object* v_r_2628_; 
v_res_2627_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(v_00_u03b2_2624_, v_x_2625_, v_x_2626_);
lean_dec(v_x_2626_);
lean_dec_ref(v_x_2625_);
v_r_2628_ = lean_box(v_res_2627_);
return v_r_2628_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_2629_, lean_object* v_x_2630_, size_t v_x_2631_, lean_object* v_x_2632_){
_start:
{
uint8_t v___x_2633_; 
v___x_2633_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2630_, v_x_2631_, v_x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2634_, lean_object* v_x_2635_, lean_object* v_x_2636_, lean_object* v_x_2637_){
_start:
{
size_t v_x_709__boxed_2638_; uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_x_709__boxed_2638_ = lean_unbox_usize(v_x_2636_);
lean_dec(v_x_2636_);
v_res_2639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_2634_, v_x_2635_, v_x_709__boxed_2638_, v_x_2637_);
lean_dec(v_x_2637_);
lean_dec_ref(v_x_2635_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2641_, lean_object* v_keys_2642_, lean_object* v_vals_2643_, lean_object* v_heq_2644_, lean_object* v_i_2645_, lean_object* v_k_2646_){
_start:
{
uint8_t v___x_2647_; 
v___x_2647_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2642_, v_i_2645_, v_k_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2648_, lean_object* v_keys_2649_, lean_object* v_vals_2650_, lean_object* v_heq_2651_, lean_object* v_i_2652_, lean_object* v_k_2653_){
_start:
{
uint8_t v_res_2654_; lean_object* v_r_2655_; 
v_res_2654_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_2648_, v_keys_2649_, v_vals_2650_, v_heq_2651_, v_i_2652_, v_k_2653_);
lean_dec(v_k_2653_);
lean_dec_ref(v_vals_2650_);
lean_dec_ref(v_keys_2649_);
v_r_2655_ = lean_box(v_res_2654_);
return v_r_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object* v_ext_2656_, lean_object* v_b_2657_, uint8_t v_kind_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_currNamespace_2662_; lean_object* v___x_2663_; lean_object* v_env_2664_; lean_object* v_nextMacroScope_2665_; lean_object* v_ngen_2666_; lean_object* v_auxDeclNGen_2667_; lean_object* v_traceState_2668_; lean_object* v_messages_2669_; lean_object* v_infoState_2670_; lean_object* v_snapshotTasks_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2683_; 
v_currNamespace_2662_ = lean_ctor_get(v___y_2659_, 6);
v___x_2663_ = lean_st_ref_take(v___y_2660_);
v_env_2664_ = lean_ctor_get(v___x_2663_, 0);
v_nextMacroScope_2665_ = lean_ctor_get(v___x_2663_, 1);
v_ngen_2666_ = lean_ctor_get(v___x_2663_, 2);
v_auxDeclNGen_2667_ = lean_ctor_get(v___x_2663_, 3);
v_traceState_2668_ = lean_ctor_get(v___x_2663_, 4);
v_messages_2669_ = lean_ctor_get(v___x_2663_, 6);
v_infoState_2670_ = lean_ctor_get(v___x_2663_, 7);
v_snapshotTasks_2671_ = lean_ctor_get(v___x_2663_, 8);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2663_, 5);
lean_dec(v_unused_2684_);
v___x_2673_ = v___x_2663_;
v_isShared_2674_ = v_isSharedCheck_2683_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_snapshotTasks_2671_);
lean_inc(v_infoState_2670_);
lean_inc(v_messages_2669_);
lean_inc(v_traceState_2668_);
lean_inc(v_auxDeclNGen_2667_);
lean_inc(v_ngen_2666_);
lean_inc(v_nextMacroScope_2665_);
lean_inc(v_env_2664_);
lean_dec(v___x_2663_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2683_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_inc(v_currNamespace_2662_);
v___x_2675_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2664_, v_ext_2656_, v_b_2657_, v_kind_2658_, v_currNamespace_2662_);
v___x_2676_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 5, v___x_2676_);
lean_ctor_set(v___x_2673_, 0, v___x_2675_);
v___x_2678_ = v___x_2673_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_nextMacroScope_2665_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_ngen_2666_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_auxDeclNGen_2667_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_traceState_2668_);
lean_ctor_set(v_reuseFailAlloc_2682_, 5, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2682_, 6, v_messages_2669_);
lean_ctor_set(v_reuseFailAlloc_2682_, 7, v_infoState_2670_);
lean_ctor_set(v_reuseFailAlloc_2682_, 8, v_snapshotTasks_2671_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_st_ref_set(v___y_2660_, v___x_2678_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_2685_, lean_object* v_b_2686_, lean_object* v_kind_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_kind_boxed_2691_; lean_object* v_res_2692_; 
v_kind_boxed_2691_ = lean_unbox(v_kind_2687_);
v_res_2692_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2685_, v_b_2686_, v_kind_boxed_2691_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object* v_00_u03b1_2693_, lean_object* v_00_u03b2_2694_, lean_object* v_00_u03c3_2695_, lean_object* v_ext_2696_, lean_object* v_b_2697_, uint8_t v_kind_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2696_, v_b_2697_, v_kind_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_00_u03b2_2704_, lean_object* v_00_u03c3_2705_, lean_object* v_ext_2706_, lean_object* v_b_2707_, lean_object* v_kind_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v_kind_boxed_2712_; lean_object* v_res_2713_; 
v_kind_boxed_2712_ = lean_unbox(v_kind_2708_);
v_res_2713_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(v_00_u03b1_2703_, v_00_u03b2_2704_, v_00_u03c3_2705_, v_ext_2706_, v_b_2707_, v_kind_boxed_2712_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
return v_res_2713_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2));
v___x_2719_ = l_Lean_stringToMessageData(v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object* v_declName_2720_, uint8_t v_kind_2721_, uint8_t v_phase_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v_env_2727_; lean_object* v_options_2728_; lean_object* v_ref_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2726_ = lean_st_ref_get(v_a_2724_);
v_env_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_ref(v_env_2727_);
lean_dec(v___x_2726_);
v_options_2728_ = lean_ctor_get(v_a_2723_, 2);
v_ref_2729_ = lean_ctor_get(v_a_2723_, 5);
lean_inc_ref(v_options_2728_);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_env_2727_);
lean_ctor_set(v___x_2730_, 1, v_options_2728_);
lean_inc(v_declName_2720_);
v___x_2731_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2720_, v___x_2730_);
lean_dec_ref(v___x_2730_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v_a_2734_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref(v___x_2731_);
lean_inc(v_declName_2720_);
v___x_2733_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2720_, v_a_2724_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref(v___x_2733_);
if (lean_obj_tag(v_a_2734_) == 1)
{
lean_object* v_val_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_val_2735_ = lean_ctor_get(v_a_2734_, 0);
lean_inc(v_val_2735_);
lean_dec_ref(v_a_2734_);
v___x_2736_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v___x_2737_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2737_, 0, v_declName_2720_);
lean_ctor_set(v___x_2737_, 1, v_val_2735_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*2, v_phase_2722_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_a_2732_);
v___x_2739_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_2736_, v___x_2738_, v_kind_2721_, v_a_2723_, v_a_2724_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v_a_2734_);
lean_dec(v_a_2732_);
v___x_2740_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1);
v___x_2741_ = 0;
v___x_2742_ = l_Lean_MessageData_ofConstName(v_declName_2720_, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2740_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2745_, v_a_2723_, v_a_2724_);
return v___x_2746_;
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_declName_2720_);
v_a_2747_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2749_ = v___x_2731_;
v_isShared_2750_ = v_isSharedCheck_2758_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2731_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2758_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2751_ = lean_io_error_to_string(v_a_2747_);
v___x_2752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
v___x_2753_ = l_Lean_MessageData_ofFormat(v___x_2752_);
lean_inc(v_ref_2729_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_ref_2729_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2754_);
v___x_2756_ = v___x_2749_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object* v_declName_2759_, lean_object* v_kind_2760_, lean_object* v_phase_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
uint8_t v_kind_boxed_2765_; uint8_t v_phase_boxed_2766_; lean_object* v_res_2767_; 
v_kind_boxed_2765_ = lean_unbox(v_kind_2760_);
v_phase_boxed_2766_ = lean_unbox(v_phase_2761_);
v_res_2767_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2759_, v_kind_boxed_2765_, v_phase_boxed_2766_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object* v_stx_2780_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = l_Lean_Syntax_isNone(v_stx_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v_inner_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2782_ = lean_unsigned_to_nat(0u);
v_inner_2783_ = l_Lean_Syntax_getArg(v_stx_2780_, v___x_2782_);
v___x_2784_ = l_Lean_Syntax_getKind(v_inner_2783_);
v___x_2785_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2));
v___x_2786_ = lean_name_eq(v___x_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4));
v___x_2788_ = lean_name_eq(v___x_2784_, v___x_2787_);
lean_dec(v___x_2784_);
if (v___x_2788_ == 0)
{
uint8_t v___x_2789_; 
v___x_2789_ = 2;
return v___x_2789_;
}
else
{
uint8_t v___x_2790_; 
v___x_2790_ = 1;
return v___x_2790_;
}
}
else
{
uint8_t v___x_2791_; 
lean_dec(v___x_2784_);
v___x_2791_ = 0;
return v___x_2791_;
}
}
else
{
uint8_t v___x_2792_; 
v___x_2792_ = 2;
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object* v_stx_2793_){
_start:
{
uint8_t v_res_2794_; lean_object* v_r_2795_; 
v_res_2794_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_2793_);
lean_dec(v_stx_2793_);
v_r_2795_ = lean_box(v_res_2794_);
return v_r_2795_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2800_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_ctor_set(v___x_2800_, 2, v___x_2799_);
lean_ctor_set(v___x_2800_, 3, v___x_2799_);
lean_ctor_set(v___x_2800_, 4, v___x_2799_);
lean_ctor_set(v___x_2800_, 5, v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_unsigned_to_nat(32u);
v___x_2802_ = lean_mk_empty_array_with_capacity(v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4(void){
_start:
{
size_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2804_ = ((size_t)5ULL);
v___x_2805_ = lean_unsigned_to_nat(0u);
v___x_2806_ = lean_unsigned_to_nat(32u);
v___x_2807_ = lean_mk_empty_array_with_capacity(v___x_2806_);
v___x_2808_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3);
v___x_2809_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2807_);
lean_ctor_set(v___x_2809_, 2, v___x_2805_);
lean_ctor_set(v___x_2809_, 3, v___x_2805_);
lean_ctor_set_usize(v___x_2809_, 4, v___x_2804_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
lean_ctor_set(v___x_2811_, 2, v___x_2810_);
lean_ctor_set(v___x_2811_, 3, v___x_2810_);
lean_ctor_set(v___x_2811_, 4, v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2812_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5);
v___x_2813_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4);
v___x_2814_ = lean_box(1);
v___x_2815_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2);
v___x_2816_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v___x_2815_);
lean_ctor_set(v___x_2817_, 2, v___x_2814_);
lean_ctor_set(v___x_2817_, 3, v___x_2813_);
lean_ctor_set(v___x_2817_, 4, v___x_2812_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object* v_declName_2818_, lean_object* v_stx_2819_, uint8_t v_attrKind_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1));
lean_inc(v_declName_2818_);
v___x_2825_ = l_Lean_ensureAttrDeclIsMeta(v___x_2824_, v_declName_2818_, v_attrKind_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v___x_2825_);
v___x_2826_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_2827_ = lean_st_mk_ref(v___x_2826_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = l_Lean_Syntax_getArg(v_stx_2819_, v___x_2828_);
v___x_2830_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_2829_);
lean_dec(v___x_2829_);
v___x_2831_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2818_, v_attrKind_2820_, v___x_2830_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2840_; 
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2841_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2840_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2840_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2835_ = lean_st_ref_get(v___x_2827_);
lean_dec(v___x_2827_);
lean_dec(v___x_2835_);
v___x_2836_ = lean_box(0);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2836_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
lean_dec(v___x_2827_);
return v___x_2831_;
}
}
else
{
lean_dec(v_declName_2818_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object* v_declName_2842_, lean_object* v_stx_2843_, lean_object* v_attrKind_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
uint8_t v_attrKind_boxed_2848_; lean_object* v_res_2849_; 
v_attrKind_boxed_2848_ = lean_unbox(v_attrKind_2844_);
v_res_2849_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_2842_, v_stx_2843_, v_attrKind_boxed_2848_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_stx_2843_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object* v_ref_2852_, lean_object* v_declName_2853_, uint8_t v_phase_2854_, lean_object* v_proc_2855_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_keys_2859_; lean_object* v___x_2860_; 
v___x_2857_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_2858_ = lean_st_ref_get(v___x_2857_);
v_keys_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc_ref(v_keys_2859_);
lean_dec(v___x_2858_);
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_2859_, v_declName_2853_);
lean_dec_ref(v_keys_2859_);
if (lean_obj_tag(v___x_2860_) == 1)
{
lean_object* v_val_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2871_; 
v_val_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2871_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_val_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2871_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2865_ = lean_st_ref_take(v_ref_2852_);
v___x_2866_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v___x_2865_, v_val_2861_, v_declName_2853_, v_phase_2854_, v_proc_2855_);
v___x_2867_ = lean_st_ref_set(v_ref_2852_, v___x_2866_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set_tag(v___x_2863_, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2867_);
v___x_2869_ = v___x_2863_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_dec(v___x_2860_);
lean_dec_ref(v_proc_2855_);
v___x_2872_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0));
v___x_2873_ = l_Lean_privateToUserName(v_declName_2853_);
v___x_2874_ = 1;
v___x_2875_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2873_, v___x_2874_);
v___x_2876_ = lean_string_append(v___x_2872_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1));
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
v___x_2879_ = lean_mk_io_user_error(v___x_2878_);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object* v_ref_2881_, lean_object* v_declName_2882_, lean_object* v_phase_2883_, lean_object* v_proc_2884_, lean_object* v_a_2885_){
_start:
{
uint8_t v_phase_boxed_2886_; lean_object* v_res_2887_; 
v_phase_boxed_2886_ = lean_unbox(v_phase_2883_);
v_res_2887_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_2881_, v_declName_2882_, v_phase_boxed_2886_, v_proc_2884_);
lean_dec(v_ref_2881_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object* v_declName_2888_, uint8_t v_phase_2889_, lean_object* v_proc_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___x_2893_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v___x_2892_, v_declName_2888_, v_phase_2889_, v_proc_2890_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object* v_declName_2894_, lean_object* v_phase_2895_, lean_object* v_proc_2896_, lean_object* v_a_2897_){
_start:
{
uint8_t v_phase_boxed_2898_; lean_object* v_res_2899_; 
v_phase_boxed_2898_ = lean_unbox(v_phase_2895_);
v_res_2899_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_2894_, v_phase_boxed_2898_, v_proc_2896_);
return v_res_2899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_box(0);
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1));
v___x_2909_ = l_Lean_mkConst(v___x_2908_, v___x_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object* v_declName_2913_, lean_object* v_stx_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v_phase_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___y_2925_; 
v___x_2918_ = lean_unsigned_to_nat(1u);
v___x_2919_ = l_Lean_Syntax_getArg(v_stx_2914_, v___x_2918_);
v_phase_2920_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_2919_);
lean_dec(v___x_2919_);
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
lean_inc(v_declName_2913_);
v___x_2923_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_2913_);
switch(v_phase_2920_)
{
case 0:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
v___y_2925_ = v___x_2957_;
goto v___jp_2924_;
}
case 1:
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
v___y_2925_ = v___x_2958_;
goto v___jp_2924_;
}
default: 
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
v___y_2925_ = v___x_2959_;
goto v___jp_2924_;
}
}
v___jp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2926_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_2927_ = lean_st_mk_ref(v___x_2926_);
lean_inc(v_declName_2913_);
v___x_2928_ = l_Lean_mkConst(v_declName_2913_, v___x_2921_);
v___x_2929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4));
v___x_2930_ = l_Lean_Name_append(v_declName_2913_, v___x_2929_);
v___x_2931_ = l_Lean_Core_mkFreshUserName(v___x_2930_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v_val_2938_; lean_object* v___x_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = lean_unsigned_to_nat(3u);
v___x_2934_ = lean_mk_empty_array_with_capacity(v___x_2933_);
v___x_2935_ = lean_array_push(v___x_2934_, v___x_2923_);
lean_inc_ref(v___y_2925_);
v___x_2936_ = lean_array_push(v___x_2935_, v___y_2925_);
v___x_2937_ = lean_array_push(v___x_2936_, v___x_2928_);
v_val_2938_ = l_Lean_mkAppN(v___x_2922_, v___x_2937_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = l_Lean_declareBuiltin(v_a_2932_, v_val_2938_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2948_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = lean_st_ref_get(v___x_2927_);
lean_dec(v___x_2927_);
lean_dec(v___x_2944_);
if (v_isShared_2943_ == 0)
{
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2940_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
lean_dec(v___x_2927_);
return v___x_2939_;
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v___x_2928_);
lean_dec(v___x_2927_);
lean_dec_ref(v___x_2923_);
v_a_2949_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2931_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2931_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object* v_declName_2960_, lean_object* v_stx_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_2960_, v_stx_2961_, v_a_2962_, v_a_2963_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_stx_2961_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3052_ = l_Lean_registerBuiltinAttribute(v___x_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_declName_3055_, lean_object* v_stx_3056_, uint8_t v_x_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3055_, v_stx_3056_, v___y_3058_, v___y_3059_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_declName_3062_, lean_object* v_stx_3063_, lean_object* v_x_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
uint8_t v_x_116__boxed_3068_; lean_object* v_res_3069_; 
v_x_116__boxed_3068_ = lean_unbox(v_x_3064_);
v_res_3069_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3062_, v_stx_3063_, v_x_116__boxed_3068_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v_stx_3063_);
return v_res_3069_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3078_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3077_, v___y_3074_, v___y_3075_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_x_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3079_, v___y_3080_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v_x_3079_);
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_unsigned_to_nat(3124561870u);
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3088_ = l_Lean_Name_num___override(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3091_ = l_Lean_Name_str___override(v___x_3090_, v___x_3089_);
return v___x_3091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3094_ = l_Lean_Name_str___override(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_unsigned_to_nat(2u);
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3097_ = l_Lean_Name_num___override(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3102_ = 1;
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3106_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3104_);
lean_ctor_set(v___x_3106_, 2, v___x_3103_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3, v___x_3102_);
return v___x_3106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___f_3107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___f_3108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___f_3108_);
lean_ctor_set(v___x_3110_, 2, v___f_3107_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3113_ = l_Lean_registerBuiltinAttribute(v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v_env_3119_; lean_object* v___x_3120_; lean_object* v_ext_3121_; lean_object* v_toEnvExtension_3122_; lean_object* v_asyncMode_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3118_ = lean_st_ref_get(v_a_3116_);
v_env_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc_ref(v_env_3119_);
lean_dec(v___x_3118_);
v___x_3120_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_3121_ = lean_ctor_get(v___x_3120_, 1);
v_toEnvExtension_3122_ = lean_ctor_get(v_ext_3121_, 0);
v_asyncMode_3123_ = lean_ctor_get(v_toEnvExtension_3122_, 2);
v___x_3124_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_3125_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3124_, v___x_3120_, v_env_3119_, v_asyncMode_3123_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3127_);
lean_dec(v_a_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3134_, v_a_3135_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
return v_res_3137_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_unsigned_to_nat(32u);
v___x_3139_ = lean_mk_empty_array_with_capacity(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3141_ = ((size_t)5ULL);
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_unsigned_to_nat(32u);
v___x_3144_ = lean_mk_empty_array_with_capacity(v___x_3143_);
v___x_3145_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0);
v___x_3146_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v___x_3144_);
lean_ctor_set(v___x_3146_, 2, v___x_3142_);
lean_ctor_set(v___x_3146_, 3, v___x_3142_);
lean_ctor_set_usize(v___x_3146_, 4, v___x_3141_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v_traceState_3150_; lean_object* v_traces_3151_; lean_object* v___x_3152_; lean_object* v_traceState_3153_; lean_object* v_env_3154_; lean_object* v_nextMacroScope_3155_; lean_object* v_ngen_3156_; lean_object* v_auxDeclNGen_3157_; lean_object* v_cache_3158_; lean_object* v_messages_3159_; lean_object* v_infoState_3160_; lean_object* v_snapshotTasks_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3180_; 
v___x_3149_ = lean_st_ref_get(v___y_3147_);
v_traceState_3150_ = lean_ctor_get(v___x_3149_, 4);
lean_inc_ref(v_traceState_3150_);
lean_dec(v___x_3149_);
v_traces_3151_ = lean_ctor_get(v_traceState_3150_, 0);
lean_inc_ref(v_traces_3151_);
lean_dec_ref(v_traceState_3150_);
v___x_3152_ = lean_st_ref_take(v___y_3147_);
v_traceState_3153_ = lean_ctor_get(v___x_3152_, 4);
v_env_3154_ = lean_ctor_get(v___x_3152_, 0);
v_nextMacroScope_3155_ = lean_ctor_get(v___x_3152_, 1);
v_ngen_3156_ = lean_ctor_get(v___x_3152_, 2);
v_auxDeclNGen_3157_ = lean_ctor_get(v___x_3152_, 3);
v_cache_3158_ = lean_ctor_get(v___x_3152_, 5);
v_messages_3159_ = lean_ctor_get(v___x_3152_, 6);
v_infoState_3160_ = lean_ctor_get(v___x_3152_, 7);
v_snapshotTasks_3161_ = lean_ctor_get(v___x_3152_, 8);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3163_ = v___x_3152_;
v_isShared_3164_ = v_isSharedCheck_3180_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_snapshotTasks_3161_);
lean_inc(v_infoState_3160_);
lean_inc(v_messages_3159_);
lean_inc(v_cache_3158_);
lean_inc(v_traceState_3153_);
lean_inc(v_auxDeclNGen_3157_);
lean_inc(v_ngen_3156_);
lean_inc(v_nextMacroScope_3155_);
lean_inc(v_env_3154_);
lean_dec(v___x_3152_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3180_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
uint64_t v_tid_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3178_; 
v_tid_3165_ = lean_ctor_get_uint64(v_traceState_3153_, sizeof(void*)*1);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_traceState_3153_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v_traceState_3153_, 0);
lean_dec(v_unused_3179_);
v___x_3167_ = v_traceState_3153_;
v_isShared_3168_ = v_isSharedCheck_3178_;
goto v_resetjp_3166_;
}
else
{
lean_dec(v_traceState_3153_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3178_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v___x_3169_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3169_);
lean_ctor_set_uint64(v_reuseFailAlloc_3177_, sizeof(void*)*1, v_tid_3165_);
v___x_3171_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3173_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v___x_3171_);
v___x_3173_ = v___x_3163_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_env_3154_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_nextMacroScope_3155_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_ngen_3156_);
lean_ctor_set(v_reuseFailAlloc_3176_, 3, v_auxDeclNGen_3157_);
lean_ctor_set(v_reuseFailAlloc_3176_, 4, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3176_, 5, v_cache_3158_);
lean_ctor_set(v_reuseFailAlloc_3176_, 6, v_messages_3159_);
lean_ctor_set(v_reuseFailAlloc_3176_, 7, v_infoState_3160_);
lean_ctor_set(v_reuseFailAlloc_3176_, 8, v_snapshotTasks_3161_);
v___x_3173_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_st_ref_set(v___y_3147_, v___x_3173_);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_traces_3151_);
return v___x_3175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3181_);
lean_dec(v___y_3181_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
return v_res_3205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object* v_opts_3206_, lean_object* v_opt_3207_){
_start:
{
lean_object* v_name_3208_; lean_object* v_defValue_3209_; lean_object* v_map_3210_; lean_object* v___x_3211_; 
v_name_3208_ = lean_ctor_get(v_opt_3207_, 0);
v_defValue_3209_ = lean_ctor_get(v_opt_3207_, 1);
v_map_3210_ = lean_ctor_get(v_opts_3206_, 0);
v___x_3211_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3210_, v_name_3208_);
if (lean_obj_tag(v___x_3211_) == 0)
{
uint8_t v___x_3212_; 
v___x_3212_ = lean_unbox(v_defValue_3209_);
return v___x_3212_;
}
else
{
lean_object* v_val_3213_; 
v_val_3213_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_val_3213_);
lean_dec_ref(v___x_3211_);
if (lean_obj_tag(v_val_3213_) == 1)
{
uint8_t v_v_3214_; 
v_v_3214_ = lean_ctor_get_uint8(v_val_3213_, 0);
lean_dec_ref(v_val_3213_);
return v_v_3214_;
}
else
{
uint8_t v___x_3215_; 
lean_dec(v_val_3213_);
v___x_3215_ = lean_unbox(v_defValue_3209_);
return v___x_3215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object* v_opts_3216_, lean_object* v_opt_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3216_, v_opt_3217_);
lean_dec_ref(v_opt_3217_);
lean_dec_ref(v_opts_3216_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t v___x_3220_, lean_object* v_e_3221_, lean_object* v_snd_3222_, lean_object* v_proc_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
if (v___x_3220_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_3221_, v_snd_3222_, v_proc_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; 
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
lean_inc(v___y_3230_);
lean_inc_ref(v___y_3229_);
lean_inc(v___y_3228_);
lean_inc_ref(v___y_3227_);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
lean_inc(v___y_3224_);
v___x_3235_ = lean_apply_11(v_proc_3223_, v_e_3221_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, lean_box(0));
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object* v___x_3236_, lean_object* v_e_3237_, lean_object* v_snd_3238_, lean_object* v_proc_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
uint8_t v___x_49151__boxed_3250_; lean_object* v_res_3251_; 
v___x_49151__boxed_3250_ = lean_unbox(v___x_3236_);
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_49151__boxed_3250_, v_e_3237_, v_snd_3238_, v_proc_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec(v_snd_3238_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(lean_object* v_msgData_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___x_3258_; lean_object* v_env_3259_; lean_object* v___x_3260_; lean_object* v_mctx_3261_; lean_object* v_lctx_3262_; lean_object* v_options_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3258_ = lean_st_ref_get(v___y_3256_);
v_env_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_ref(v_env_3259_);
lean_dec(v___x_3258_);
v___x_3260_ = lean_st_ref_get(v___y_3254_);
v_mctx_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc_ref(v_mctx_3261_);
lean_dec(v___x_3260_);
v_lctx_3262_ = lean_ctor_get(v___y_3253_, 2);
v_options_3263_ = lean_ctor_get(v___y_3255_, 2);
lean_inc_ref(v_options_3263_);
lean_inc_ref(v_lctx_3262_);
v___x_3264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3264_, 0, v_env_3259_);
lean_ctor_set(v___x_3264_, 1, v_mctx_3261_);
lean_ctor_set(v___x_3264_, 2, v_lctx_3262_);
lean_ctor_set(v___x_3264_, 3, v_options_3263_);
v___x_3265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v_msgData_3252_);
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(v_msgData_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(size_t v_sz_3274_, size_t v_i_3275_, lean_object* v_bs_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_usize_dec_lt(v_i_3275_, v_sz_3274_);
if (v___x_3277_ == 0)
{
return v_bs_3276_;
}
else
{
lean_object* v_v_3278_; lean_object* v_msg_3279_; lean_object* v___x_3280_; lean_object* v_bs_x27_3281_; size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; 
v_v_3278_ = lean_array_uget_borrowed(v_bs_3276_, v_i_3275_);
v_msg_3279_ = lean_ctor_get(v_v_3278_, 1);
lean_inc_ref(v_msg_3279_);
v___x_3280_ = lean_unsigned_to_nat(0u);
v_bs_x27_3281_ = lean_array_uset(v_bs_3276_, v_i_3275_, v___x_3280_);
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_add(v_i_3275_, v___x_3282_);
v___x_3284_ = lean_array_uset(v_bs_x27_3281_, v_i_3275_, v_msg_3279_);
v_i_3275_ = v___x_3283_;
v_bs_3276_ = v___x_3284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_3286_, lean_object* v_i_3287_, lean_object* v_bs_3288_){
_start:
{
size_t v_sz_boxed_3289_; size_t v_i_boxed_3290_; lean_object* v_res_3291_; 
v_sz_boxed_3289_ = lean_unbox_usize(v_sz_3286_);
lean_dec(v_sz_3286_);
v_i_boxed_3290_ = lean_unbox_usize(v_i_3287_);
lean_dec(v_i_3287_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(v_sz_boxed_3289_, v_i_boxed_3290_, v_bs_3288_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object* v_oldTraces_3292_, lean_object* v_data_3293_, lean_object* v_ref_3294_, lean_object* v_msg_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_fileName_3301_; lean_object* v_fileMap_3302_; lean_object* v_options_3303_; lean_object* v_currRecDepth_3304_; lean_object* v_maxRecDepth_3305_; lean_object* v_ref_3306_; lean_object* v_currNamespace_3307_; lean_object* v_openDecls_3308_; lean_object* v_initHeartbeats_3309_; lean_object* v_maxHeartbeats_3310_; lean_object* v_quotContext_3311_; lean_object* v_currMacroScope_3312_; uint8_t v_diag_3313_; lean_object* v_cancelTk_x3f_3314_; uint8_t v_suppressElabErrors_3315_; lean_object* v_inheritedTraceOptions_3316_; lean_object* v___x_3317_; lean_object* v_traceState_3318_; lean_object* v_traces_3319_; lean_object* v_ref_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; size_t v_sz_3323_; size_t v___x_3324_; lean_object* v___x_3325_; lean_object* v_msg_3326_; lean_object* v___x_3327_; lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3365_; 
v_fileName_3301_ = lean_ctor_get(v___y_3298_, 0);
v_fileMap_3302_ = lean_ctor_get(v___y_3298_, 1);
v_options_3303_ = lean_ctor_get(v___y_3298_, 2);
v_currRecDepth_3304_ = lean_ctor_get(v___y_3298_, 3);
v_maxRecDepth_3305_ = lean_ctor_get(v___y_3298_, 4);
v_ref_3306_ = lean_ctor_get(v___y_3298_, 5);
v_currNamespace_3307_ = lean_ctor_get(v___y_3298_, 6);
v_openDecls_3308_ = lean_ctor_get(v___y_3298_, 7);
v_initHeartbeats_3309_ = lean_ctor_get(v___y_3298_, 8);
v_maxHeartbeats_3310_ = lean_ctor_get(v___y_3298_, 9);
v_quotContext_3311_ = lean_ctor_get(v___y_3298_, 10);
v_currMacroScope_3312_ = lean_ctor_get(v___y_3298_, 11);
v_diag_3313_ = lean_ctor_get_uint8(v___y_3298_, sizeof(void*)*14);
v_cancelTk_x3f_3314_ = lean_ctor_get(v___y_3298_, 12);
v_suppressElabErrors_3315_ = lean_ctor_get_uint8(v___y_3298_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3316_ = lean_ctor_get(v___y_3298_, 13);
v___x_3317_ = lean_st_ref_get(v___y_3299_);
v_traceState_3318_ = lean_ctor_get(v___x_3317_, 4);
lean_inc_ref(v_traceState_3318_);
lean_dec(v___x_3317_);
v_traces_3319_ = lean_ctor_get(v_traceState_3318_, 0);
lean_inc_ref(v_traces_3319_);
lean_dec_ref(v_traceState_3318_);
v_ref_3320_ = l_Lean_replaceRef(v_ref_3294_, v_ref_3306_);
lean_inc_ref(v_inheritedTraceOptions_3316_);
lean_inc(v_cancelTk_x3f_3314_);
lean_inc(v_currMacroScope_3312_);
lean_inc(v_quotContext_3311_);
lean_inc(v_maxHeartbeats_3310_);
lean_inc(v_initHeartbeats_3309_);
lean_inc(v_openDecls_3308_);
lean_inc(v_currNamespace_3307_);
lean_inc(v_maxRecDepth_3305_);
lean_inc(v_currRecDepth_3304_);
lean_inc_ref(v_options_3303_);
lean_inc_ref(v_fileMap_3302_);
lean_inc_ref(v_fileName_3301_);
v___x_3321_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3321_, 0, v_fileName_3301_);
lean_ctor_set(v___x_3321_, 1, v_fileMap_3302_);
lean_ctor_set(v___x_3321_, 2, v_options_3303_);
lean_ctor_set(v___x_3321_, 3, v_currRecDepth_3304_);
lean_ctor_set(v___x_3321_, 4, v_maxRecDepth_3305_);
lean_ctor_set(v___x_3321_, 5, v_ref_3320_);
lean_ctor_set(v___x_3321_, 6, v_currNamespace_3307_);
lean_ctor_set(v___x_3321_, 7, v_openDecls_3308_);
lean_ctor_set(v___x_3321_, 8, v_initHeartbeats_3309_);
lean_ctor_set(v___x_3321_, 9, v_maxHeartbeats_3310_);
lean_ctor_set(v___x_3321_, 10, v_quotContext_3311_);
lean_ctor_set(v___x_3321_, 11, v_currMacroScope_3312_);
lean_ctor_set(v___x_3321_, 12, v_cancelTk_x3f_3314_);
lean_ctor_set(v___x_3321_, 13, v_inheritedTraceOptions_3316_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*14, v_diag_3313_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*14 + 1, v_suppressElabErrors_3315_);
v___x_3322_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3319_);
lean_dec_ref(v_traces_3319_);
v_sz_3323_ = lean_array_size(v___x_3322_);
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(v_sz_3323_, v___x_3324_, v___x_3322_);
v_msg_3326_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3326_, 0, v_data_3293_);
lean_ctor_set(v_msg_3326_, 1, v_msg_3295_);
lean_ctor_set(v_msg_3326_, 2, v___x_3325_);
v___x_3327_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(v_msg_3326_, v___y_3296_, v___y_3297_, v___x_3321_, v___y_3299_);
lean_dec_ref(v___x_3321_);
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3365_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3365_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v_traceState_3333_; lean_object* v_env_3334_; lean_object* v_nextMacroScope_3335_; lean_object* v_ngen_3336_; lean_object* v_auxDeclNGen_3337_; lean_object* v_cache_3338_; lean_object* v_messages_3339_; lean_object* v_infoState_3340_; lean_object* v_snapshotTasks_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3364_; 
v___x_3332_ = lean_st_ref_take(v___y_3299_);
v_traceState_3333_ = lean_ctor_get(v___x_3332_, 4);
v_env_3334_ = lean_ctor_get(v___x_3332_, 0);
v_nextMacroScope_3335_ = lean_ctor_get(v___x_3332_, 1);
v_ngen_3336_ = lean_ctor_get(v___x_3332_, 2);
v_auxDeclNGen_3337_ = lean_ctor_get(v___x_3332_, 3);
v_cache_3338_ = lean_ctor_get(v___x_3332_, 5);
v_messages_3339_ = lean_ctor_get(v___x_3332_, 6);
v_infoState_3340_ = lean_ctor_get(v___x_3332_, 7);
v_snapshotTasks_3341_ = lean_ctor_get(v___x_3332_, 8);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3343_ = v___x_3332_;
v_isShared_3344_ = v_isSharedCheck_3364_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_snapshotTasks_3341_);
lean_inc(v_infoState_3340_);
lean_inc(v_messages_3339_);
lean_inc(v_cache_3338_);
lean_inc(v_traceState_3333_);
lean_inc(v_auxDeclNGen_3337_);
lean_inc(v_ngen_3336_);
lean_inc(v_nextMacroScope_3335_);
lean_inc(v_env_3334_);
lean_dec(v___x_3332_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3364_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
uint64_t v_tid_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3362_; 
v_tid_3345_ = lean_ctor_get_uint64(v_traceState_3333_, sizeof(void*)*1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_traceState_3333_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v_traceState_3333_, 0);
lean_dec(v_unused_3363_);
v___x_3347_ = v_traceState_3333_;
v_isShared_3348_ = v_isSharedCheck_3362_;
goto v_resetjp_3346_;
}
else
{
lean_dec(v_traceState_3333_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3362_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v_ref_3294_);
lean_ctor_set(v___x_3349_, 1, v_a_3328_);
v___x_3350_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3292_, v___x_3349_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3350_);
v___x_3352_ = v___x_3347_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3350_);
lean_ctor_set_uint64(v_reuseFailAlloc_3361_, sizeof(void*)*1, v_tid_3345_);
v___x_3352_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3354_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3352_);
v___x_3354_ = v___x_3343_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_env_3334_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_nextMacroScope_3335_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_ngen_3336_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v_auxDeclNGen_3337_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3360_, 5, v_cache_3338_);
lean_ctor_set(v_reuseFailAlloc_3360_, 6, v_messages_3339_);
lean_ctor_set(v_reuseFailAlloc_3360_, 7, v_infoState_3340_);
lean_ctor_set(v_reuseFailAlloc_3360_, 8, v_snapshotTasks_3341_);
v___x_3354_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3355_ = lean_st_ref_set(v___y_3299_, v___x_3354_);
v___x_3356_ = lean_box(0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3356_);
v___x_3358_ = v___x_3330_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_3366_, lean_object* v_data_3367_, lean_object* v_ref_3368_, lean_object* v_msg_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_oldTraces_3366_, v_data_3367_, v_ref_3368_, v_msg_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
return v_res_3375_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object* v_e_3376_){
_start:
{
if (lean_obj_tag(v_e_3376_) == 0)
{
uint8_t v___x_3377_; 
v___x_3377_ = 2;
return v___x_3377_;
}
else
{
uint8_t v___x_3378_; 
v___x_3378_ = 0;
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object* v_e_3379_){
_start:
{
uint8_t v_res_3380_; lean_object* v_r_3381_; 
v_res_3380_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_e_3379_);
lean_dec_ref(v_e_3379_);
v_r_3381_ = lean_box(v_res_3380_);
return v_r_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object* v_opts_3382_, lean_object* v_opt_3383_){
_start:
{
lean_object* v_name_3384_; lean_object* v_defValue_3385_; lean_object* v_map_3386_; lean_object* v___x_3387_; 
v_name_3384_ = lean_ctor_get(v_opt_3383_, 0);
v_defValue_3385_ = lean_ctor_get(v_opt_3383_, 1);
v_map_3386_ = lean_ctor_get(v_opts_3382_, 0);
v___x_3387_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3386_, v_name_3384_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_inc(v_defValue_3385_);
return v_defValue_3385_;
}
else
{
lean_object* v_val_3388_; 
v_val_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_val_3388_);
lean_dec_ref(v___x_3387_);
if (lean_obj_tag(v_val_3388_) == 3)
{
lean_object* v_v_3389_; 
v_v_3389_ = lean_ctor_get(v_val_3388_, 0);
lean_inc(v_v_3389_);
lean_dec_ref(v_val_3388_);
return v_v_3389_;
}
else
{
lean_dec(v_val_3388_);
lean_inc(v_defValue_3385_);
return v_defValue_3385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object* v_opts_3390_, lean_object* v_opt_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3390_, v_opt_3391_);
lean_dec_ref(v_opt_3391_);
lean_dec_ref(v_opts_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3393_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_a_3395_ = lean_ctor_get(v_x_3393_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_x_3393_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v_x_3393_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v_x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 1);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v_x_3393_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_x_3393_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v_x_3393_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v_x_3393_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set_tag(v___x_3405_, 0);
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg___boxed(lean_object* v_x_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_x_3411_);
return v_res_3413_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0));
v___x_3416_ = l_Lean_stringToMessageData(v___x_3415_);
return v___x_3416_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3417_; double v___x_3418_; 
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_float_of_nat(v___x_3417_);
return v___x_3418_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3));
v___x_3421_ = l_Lean_stringToMessageData(v___x_3420_);
return v___x_3421_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3422_; double v___x_3423_; 
v___x_3422_ = lean_unsigned_to_nat(1000u);
v___x_3423_ = lean_float_of_nat(v___x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object* v_cls_3424_, uint8_t v_collapsed_3425_, lean_object* v_tag_3426_, lean_object* v_opts_3427_, uint8_t v_clsEnabled_3428_, lean_object* v_oldTraces_3429_, lean_object* v_msg_3430_, lean_object* v_resStartStop_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3541_; 
v_fst_3442_ = lean_ctor_get(v_resStartStop_3431_, 0);
v_snd_3443_ = lean_ctor_get(v_resStartStop_3431_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_resStartStop_3431_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3445_ = v_resStartStop_3431_;
v_isShared_3446_ = v_isSharedCheck_3541_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_inc(v_fst_3442_);
lean_dec(v_resStartStop_3431_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3541_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v_data_3450_; lean_object* v_fst_3461_; lean_object* v_snd_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3540_; 
v_fst_3461_ = lean_ctor_get(v_snd_3443_, 0);
v_snd_3462_ = lean_ctor_get(v_snd_3443_, 1);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_snd_3443_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3464_ = v_snd_3443_;
v_isShared_3465_ = v_isSharedCheck_3540_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_snd_3462_);
lean_inc(v_fst_3461_);
lean_dec(v_snd_3443_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3540_;
goto v_resetjp_3463_;
}
v___jp_3447_:
{
lean_object* v___x_3451_; 
lean_inc(v___y_3449_);
v___x_3451_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_oldTraces_3429_, v_data_3450_, v___y_3449_, v___y_3448_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref(v___x_3451_);
v___x_3452_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_fst_3442_);
return v___x_3452_;
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v_fst_3442_);
v_a_3453_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3451_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; uint8_t v___x_3467_; lean_object* v___y_3469_; lean_object* v_a_3470_; uint8_t v___y_3494_; double v___y_3525_; 
v___x_3466_ = l_Lean_trace_profiler;
v___x_3467_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3427_, v___x_3466_);
if (v___x_3467_ == 0)
{
v___y_3494_ = v___x_3467_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3530_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3531_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3427_, v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; double v___x_3534_; double v___x_3535_; double v___x_3536_; 
v___x_3532_ = l_Lean_trace_profiler_threshold;
v___x_3533_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3427_, v___x_3532_);
v___x_3534_ = lean_float_of_nat(v___x_3533_);
v___x_3535_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5);
v___x_3536_ = lean_float_div(v___x_3534_, v___x_3535_);
v___y_3525_ = v___x_3536_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; double v___x_3539_; 
v___x_3537_ = l_Lean_trace_profiler_threshold;
v___x_3538_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3427_, v___x_3537_);
v___x_3539_ = lean_float_of_nat(v___x_3538_);
v___y_3525_ = v___x_3539_;
goto v___jp_3524_;
}
}
v___jp_3468_:
{
uint8_t v_result_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v_result_3471_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_fst_3442_);
v___x_3472_ = l_Lean_TraceResult_toEmoji(v_result_3471_);
v___x_3473_ = l_Lean_stringToMessageData(v___x_3472_);
v___x_3474_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1);
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 7);
lean_ctor_set(v___x_3464_, 1, v___x_3474_);
lean_ctor_set(v___x_3464_, 0, v___x_3473_);
v___x_3476_ = v___x_3464_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v_m_3478_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 7);
lean_ctor_set(v___x_3445_, 1, v_a_3470_);
lean_ctor_set(v___x_3445_, 0, v___x_3476_);
v_m_3478_ = v___x_3445_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_a_3470_);
v_m_3478_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; double v___x_3481_; lean_object* v_data_3482_; 
v___x_3479_ = lean_box(v_result_3471_);
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
v___x_3481_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2);
lean_inc_ref(v_tag_3426_);
lean_inc_ref(v___x_3480_);
lean_inc(v_cls_3424_);
v_data_3482_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3482_, 0, v_cls_3424_);
lean_ctor_set(v_data_3482_, 1, v___x_3480_);
lean_ctor_set(v_data_3482_, 2, v_tag_3426_);
lean_ctor_set_float(v_data_3482_, sizeof(void*)*3, v___x_3481_);
lean_ctor_set_float(v_data_3482_, sizeof(void*)*3 + 8, v___x_3481_);
lean_ctor_set_uint8(v_data_3482_, sizeof(void*)*3 + 16, v_collapsed_3425_);
if (v___x_3467_ == 0)
{
lean_dec_ref(v___x_3480_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_dec_ref(v_tag_3426_);
lean_dec(v_cls_3424_);
v___y_3448_ = v_m_3478_;
v___y_3449_ = v___y_3469_;
v_data_3450_ = v_data_3482_;
goto v___jp_3447_;
}
else
{
lean_object* v_data_3483_; double v___x_3484_; double v___x_3485_; 
lean_dec_ref(v_data_3482_);
v_data_3483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3483_, 0, v_cls_3424_);
lean_ctor_set(v_data_3483_, 1, v___x_3480_);
lean_ctor_set(v_data_3483_, 2, v_tag_3426_);
v___x_3484_ = lean_unbox_float(v_fst_3461_);
lean_dec(v_fst_3461_);
lean_ctor_set_float(v_data_3483_, sizeof(void*)*3, v___x_3484_);
v___x_3485_ = lean_unbox_float(v_snd_3462_);
lean_dec(v_snd_3462_);
lean_ctor_set_float(v_data_3483_, sizeof(void*)*3 + 8, v___x_3485_);
lean_ctor_set_uint8(v_data_3483_, sizeof(void*)*3 + 16, v_collapsed_3425_);
v___y_3448_ = v_m_3478_;
v___y_3449_ = v___y_3469_;
v_data_3450_ = v_data_3483_;
goto v___jp_3447_;
}
}
}
}
v___jp_3488_:
{
lean_object* v_ref_3489_; lean_object* v___x_3490_; 
v_ref_3489_ = lean_ctor_get(v___y_3439_, 5);
lean_inc(v___y_3440_);
lean_inc_ref(v___y_3439_);
lean_inc(v___y_3438_);
lean_inc_ref(v___y_3437_);
lean_inc(v___y_3436_);
lean_inc_ref(v___y_3435_);
lean_inc(v___y_3434_);
lean_inc_ref(v___y_3433_);
lean_inc(v___y_3432_);
lean_inc(v_fst_3442_);
v___x_3490_ = lean_apply_11(v_msg_3430_, v_fst_3442_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, lean_box(0));
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3490_);
v___y_3469_ = v_ref_3489_;
v_a_3470_ = v_a_3491_;
goto v___jp_3468_;
}
else
{
lean_object* v___x_3492_; 
lean_dec_ref(v___x_3490_);
v___x_3492_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4);
v___y_3469_ = v_ref_3489_;
v_a_3470_ = v___x_3492_;
goto v___jp_3468_;
}
}
v___jp_3493_:
{
if (v_clsEnabled_3428_ == 0)
{
if (v___y_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v_traceState_3496_; lean_object* v_env_3497_; lean_object* v_nextMacroScope_3498_; lean_object* v_ngen_3499_; lean_object* v_auxDeclNGen_3500_; lean_object* v_cache_3501_; lean_object* v_messages_3502_; lean_object* v_infoState_3503_; lean_object* v_snapshotTasks_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_3464_);
lean_dec(v_snd_3462_);
lean_dec(v_fst_3461_);
lean_del_object(v___x_3445_);
lean_dec_ref(v_msg_3430_);
lean_dec_ref(v_tag_3426_);
lean_dec(v_cls_3424_);
v___x_3495_ = lean_st_ref_take(v___y_3440_);
v_traceState_3496_ = lean_ctor_get(v___x_3495_, 4);
v_env_3497_ = lean_ctor_get(v___x_3495_, 0);
v_nextMacroScope_3498_ = lean_ctor_get(v___x_3495_, 1);
v_ngen_3499_ = lean_ctor_get(v___x_3495_, 2);
v_auxDeclNGen_3500_ = lean_ctor_get(v___x_3495_, 3);
v_cache_3501_ = lean_ctor_get(v___x_3495_, 5);
v_messages_3502_ = lean_ctor_get(v___x_3495_, 6);
v_infoState_3503_ = lean_ctor_get(v___x_3495_, 7);
v_snapshotTasks_3504_ = lean_ctor_get(v___x_3495_, 8);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3506_ = v___x_3495_;
v_isShared_3507_ = v_isSharedCheck_3523_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_snapshotTasks_3504_);
lean_inc(v_infoState_3503_);
lean_inc(v_messages_3502_);
lean_inc(v_cache_3501_);
lean_inc(v_traceState_3496_);
lean_inc(v_auxDeclNGen_3500_);
lean_inc(v_ngen_3499_);
lean_inc(v_nextMacroScope_3498_);
lean_inc(v_env_3497_);
lean_dec(v___x_3495_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3523_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
uint64_t v_tid_3508_; lean_object* v_traces_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3522_; 
v_tid_3508_ = lean_ctor_get_uint64(v_traceState_3496_, sizeof(void*)*1);
v_traces_3509_ = lean_ctor_get(v_traceState_3496_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_traceState_3496_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3511_ = v_traceState_3496_;
v_isShared_3512_ = v_isSharedCheck_3522_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_traces_3509_);
lean_dec(v_traceState_3496_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3522_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3429_, v_traces_3509_);
lean_dec_ref(v_traces_3509_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3513_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3513_);
lean_ctor_set_uint64(v_reuseFailAlloc_3521_, sizeof(void*)*1, v_tid_3508_);
v___x_3515_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 4, v___x_3515_);
v___x_3517_ = v___x_3506_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_env_3497_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_nextMacroScope_3498_);
lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_ngen_3499_);
lean_ctor_set(v_reuseFailAlloc_3520_, 3, v_auxDeclNGen_3500_);
lean_ctor_set(v_reuseFailAlloc_3520_, 4, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3520_, 5, v_cache_3501_);
lean_ctor_set(v_reuseFailAlloc_3520_, 6, v_messages_3502_);
lean_ctor_set(v_reuseFailAlloc_3520_, 7, v_infoState_3503_);
lean_ctor_set(v_reuseFailAlloc_3520_, 8, v_snapshotTasks_3504_);
v___x_3517_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_st_ref_set(v___y_3440_, v___x_3517_);
v___x_3519_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_fst_3442_);
return v___x_3519_;
}
}
}
}
}
else
{
goto v___jp_3488_;
}
}
else
{
goto v___jp_3488_;
}
}
v___jp_3524_:
{
double v___x_3526_; double v___x_3527_; double v___x_3528_; uint8_t v___x_3529_; 
v___x_3526_ = lean_unbox_float(v_snd_3462_);
v___x_3527_ = lean_unbox_float(v_fst_3461_);
v___x_3528_ = lean_float_sub(v___x_3526_, v___x_3527_);
v___x_3529_ = lean_float_decLt(v___y_3525_, v___x_3528_);
v___y_3494_ = v___x_3529_;
goto v___jp_3493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object** _args){
lean_object* v_cls_3542_ = _args[0];
lean_object* v_collapsed_3543_ = _args[1];
lean_object* v_tag_3544_ = _args[2];
lean_object* v_opts_3545_ = _args[3];
lean_object* v_clsEnabled_3546_ = _args[4];
lean_object* v_oldTraces_3547_ = _args[5];
lean_object* v_msg_3548_ = _args[6];
lean_object* v_resStartStop_3549_ = _args[7];
lean_object* v___y_3550_ = _args[8];
lean_object* v___y_3551_ = _args[9];
lean_object* v___y_3552_ = _args[10];
lean_object* v___y_3553_ = _args[11];
lean_object* v___y_3554_ = _args[12];
lean_object* v___y_3555_ = _args[13];
lean_object* v___y_3556_ = _args[14];
lean_object* v___y_3557_ = _args[15];
lean_object* v___y_3558_ = _args[16];
lean_object* v___y_3559_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3560_; uint8_t v_clsEnabled_boxed_3561_; lean_object* v_res_3562_; 
v_collapsed_boxed_3560_ = lean_unbox(v_collapsed_3543_);
v_clsEnabled_boxed_3561_ = lean_unbox(v_clsEnabled_3546_);
v_res_3562_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_3542_, v_collapsed_boxed_3560_, v_tag_3544_, v_opts_3545_, v_clsEnabled_boxed_3561_, v_oldTraces_3547_, v_msg_3548_, v_resStartStop_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v_opts_3545_);
return v_res_3562_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2));
v___x_3568_ = l_Lean_stringToMessageData(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4));
v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6));
v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8));
v___x_3577_ = l_Lean_stringToMessageData(v___x_3576_);
return v___x_3577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10));
v___x_3580_ = l_Lean_stringToMessageData(v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object* v___x_3581_, lean_object* v_e_3582_, lean_object* v_x_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v_e_3582_);
v_a_3594_ = lean_ctor_get(v_x_3583_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_x_3583_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3596_ = v_x_3583_;
v_isShared_3597_ = v_isSharedCheck_3608_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v_x_3583_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3608_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3599_ = l_Lean_MessageData_ofName(v___x_3581_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l_Lean_Exception_toMessageData(v_a_3594_);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 0, v___x_3604_);
v___x_3606_ = v___x_3596_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3647_; 
v_a_3609_ = lean_ctor_get(v_x_3583_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_x_3583_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3611_ = v_x_3583_;
v_isShared_3612_ = v_isSharedCheck_3647_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v_x_3583_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3647_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
if (lean_obj_tag(v_a_3609_) == 0)
{
uint8_t v_done_3613_; 
v_done_3613_ = lean_ctor_get_uint8(v_a_3609_, 0);
lean_dec_ref(v_a_3609_);
if (v_done_3613_ == 1)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3615_ = l_Lean_MessageData_ofName(v___x_3581_);
v___x_3616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l_Lean_indentExpr(v_e_3582_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3620_);
v___x_3622_ = v___x_3611_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
lean_dec_ref(v_e_3582_);
v___x_3624_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3625_ = l_Lean_MessageData_ofName(v___x_3581_);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3628_);
v___x_3630_ = v___x_3611_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
else
{
lean_object* v_e_x27_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3645_; 
v_e_x27_3632_ = lean_ctor_get(v_a_3609_, 0);
lean_inc_ref(v_e_x27_3632_);
lean_dec_ref(v_a_3609_);
v___x_3633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3634_ = l_Lean_MessageData_ofName(v___x_3581_);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9);
v___x_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3635_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___x_3638_ = l_Lean_indentExpr(v_e_3582_);
v___x_3639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3637_);
lean_ctor_set(v___x_3639_, 1, v___x_3638_);
v___x_3640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11);
v___x_3641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3639_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = l_Lean_indentExpr(v_e_x27_3632_);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3643_);
v___x_3645_ = v___x_3611_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object* v___x_3648_, lean_object* v_e_3649_, lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_3648_, v_e_3649_, v_x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
return v_res_3661_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8));
v___x_3688_ = l_Lean_Name_append(v___x_3687_, v___x_3686_);
return v___x_3688_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10(void){
_start:
{
lean_object* v___x_3689_; double v___x_3690_; 
v___x_3689_ = lean_unsigned_to_nat(1000000000u);
v___x_3690_ = lean_float_of_nat(v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object* v_erased_3691_, lean_object* v_e_3692_, lean_object* v_as_3693_, size_t v_sz_3694_, size_t v_i_3695_, lean_object* v_b_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_a_3708_; uint8_t v___x_3712_; 
v___x_3712_ = lean_usize_dec_lt(v_i_3695_, v_sz_3694_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_dec_ref(v_e_3692_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v_b_3696_);
return v___x_3713_;
}
else
{
lean_object* v_a_3714_; lean_object* v_fst_3715_; lean_object* v_toCbvSimprocOLeanEntry_3716_; lean_object* v_snd_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v_b_3696_);
v_a_3714_ = lean_array_uget(v_as_3693_, v_i_3695_);
v_fst_3715_ = lean_ctor_get(v_a_3714_, 0);
lean_inc(v_fst_3715_);
v_toCbvSimprocOLeanEntry_3716_ = lean_ctor_get(v_fst_3715_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_3716_);
v_snd_3717_ = lean_ctor_get(v_a_3714_, 1);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_a_3714_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v_a_3714_, 0);
lean_dec(v_unused_3859_);
v___x_3719_ = v_a_3714_;
v_isShared_3720_ = v_isSharedCheck_3858_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_snd_3717_);
lean_dec(v_a_3714_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3858_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v_proc_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3856_; 
v_proc_3721_ = lean_ctor_get(v_fst_3715_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_fst_3715_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; 
v_unused_3857_ = lean_ctor_get(v_fst_3715_, 0);
lean_dec(v_unused_3857_);
v___x_3723_ = v_fst_3715_;
v_isShared_3724_ = v_isSharedCheck_3856_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_proc_3721_);
lean_dec(v_fst_3715_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3856_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_declName_3725_; lean_object* v___x_3726_; lean_object* v___y_3728_; lean_object* v___x_3734_; uint8_t v___x_3735_; lean_object* v___y_3737_; 
v_declName_3725_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_3716_, 0);
lean_inc(v_declName_3725_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_3716_);
v___x_3726_ = lean_box(0);
v___x_3734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v___x_3735_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_3691_, v_declName_3725_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3760_; lean_object* v_options_3761_; lean_object* v_inheritedTraceOptions_3762_; uint8_t v_hasTrace_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1));
v_options_3761_ = lean_ctor_get(v___y_3704_, 2);
v_inheritedTraceOptions_3762_ = lean_ctor_get(v___y_3704_, 13);
v_hasTrace_3763_ = lean_ctor_get_uint8(v_options_3761_, sizeof(void*)*1);
v___x_3764_ = lean_unsigned_to_nat(0u);
v___x_3765_ = lean_nat_dec_eq(v_snd_3717_, v___x_3764_);
if (v_hasTrace_3763_ == 0)
{
lean_object* v___x_3766_; 
lean_dec(v_declName_3725_);
lean_inc_ref(v_e_3692_);
v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3765_, v_e_3692_, v_snd_3717_, v_proc_3721_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v_snd_3717_);
v___y_3737_ = v___x_3766_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___f_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_a_3780_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_a_3795_; 
v___x_3767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2));
v___x_3768_ = l_Lean_privateToUserName(v_declName_3725_);
v___x_3769_ = lean_box(0);
v___x_3770_ = l_Lean_Name_replacePrefix(v___x_3768_, v___x_3760_, v___x_3769_);
v___x_3771_ = l_Lean_Name_replacePrefix(v___x_3770_, v___x_3767_, v___x_3769_);
lean_inc_ref(v_e_3692_);
v___f_3772_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed), 13, 2);
lean_closure_set(v___f_3772_, 0, v___x_3771_);
lean_closure_set(v___f_3772_, 1, v_e_3692_);
v___x_3773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6));
v___x_3775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9);
v___x_3776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3762_, v_options_3761_, v___x_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = l_Lean_trace_profiler;
v___x_3854_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3761_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v___f_3772_);
lean_inc_ref(v_e_3692_);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3765_, v_e_3692_, v_snd_3717_, v_proc_3721_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v_snd_3717_);
v___y_3737_ = v___x_3855_;
goto v___jp_3736_;
}
else
{
goto v___jp_3804_;
}
}
else
{
goto v___jp_3804_;
}
v___jp_3777_:
{
lean_object* v___x_3781_; double v___x_3782_; double v___x_3783_; double v___x_3784_; double v___x_3785_; double v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3781_ = lean_io_mono_nanos_now();
v___x_3782_ = lean_float_of_nat(v___y_3778_);
v___x_3783_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10);
v___x_3784_ = lean_float_div(v___x_3782_, v___x_3783_);
v___x_3785_ = lean_float_of_nat(v___x_3781_);
v___x_3786_ = lean_float_div(v___x_3785_, v___x_3783_);
v___x_3787_ = lean_box_float(v___x_3784_);
v___x_3788_ = lean_box_float(v___x_3786_);
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v_a_3780_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3773_, v_hasTrace_3763_, v___x_3774_, v_options_3761_, v___x_3776_, v___y_3779_, v___f_3772_, v___x_3790_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
v___y_3737_ = v___x_3791_;
goto v___jp_3736_;
}
v___jp_3792_:
{
lean_object* v___x_3796_; double v___x_3797_; double v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3796_ = lean_io_get_num_heartbeats();
v___x_3797_ = lean_float_of_nat(v___y_3794_);
v___x_3798_ = lean_float_of_nat(v___x_3796_);
v___x_3799_ = lean_box_float(v___x_3797_);
v___x_3800_ = lean_box_float(v___x_3798_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v_a_3795_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_3773_, v_hasTrace_3763_, v___x_3774_, v_options_3761_, v___x_3776_, v___y_3793_, v___f_3772_, v___x_3802_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
v___y_3737_ = v___x_3803_;
goto v___jp_3736_;
}
v___jp_3804_:
{
lean_object* v___x_3805_; 
v___x_3805_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3705_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref(v___x_3805_);
v___x_3807_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3808_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_3761_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = lean_io_mono_nanos_now();
lean_inc_ref(v_e_3692_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3765_, v_e_3692_, v_snd_3717_, v_proc_3721_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v_snd_3717_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 1);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
v___y_3778_ = v___x_3809_;
v___y_3779_ = v_a_3806_;
v_a_3780_ = v___x_3816_;
goto v___jp_3777_;
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
v_a_3819_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3810_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3810_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 0);
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
v___y_3778_ = v___x_3809_;
v___y_3779_ = v_a_3806_;
v_a_3780_ = v___x_3824_;
goto v___jp_3777_;
}
}
}
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_e_3692_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3765_, v_e_3692_, v_snd_3717_, v_proc_3721_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v_snd_3717_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set_tag(v___x_3831_, 1);
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
v___y_3793_ = v_a_3806_;
v___y_3794_ = v___x_3827_;
v_a_3795_ = v___x_3834_;
goto v___jp_3792_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3828_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3828_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set_tag(v___x_3839_, 0);
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
v___y_3793_ = v_a_3806_;
v___y_3794_ = v___x_3827_;
v_a_3795_ = v___x_3842_;
goto v___jp_3792_;
}
}
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec_ref(v___f_3772_);
lean_del_object(v___x_3723_);
lean_dec_ref(v_proc_3721_);
lean_del_object(v___x_3719_);
lean_dec(v_snd_3717_);
lean_dec_ref(v_e_3692_);
v_a_3845_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3805_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3805_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_3725_);
lean_del_object(v___x_3723_);
lean_dec_ref(v_proc_3721_);
lean_del_object(v___x_3719_);
lean_dec(v_snd_3717_);
v_a_3708_ = v___x_3734_;
goto v___jp_3707_;
}
v___jp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___y_3728_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 1, v___x_3726_);
lean_ctor_set(v___x_3719_, 0, v___x_3729_);
v___x_3731_ = v___x_3719_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v___x_3726_);
v___x_3731_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
v___jp_3736_:
{
if (lean_obj_tag(v___y_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3751_; 
v_a_3738_ = lean_ctor_get(v___y_3737_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___y_3737_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3740_ = v___y_3737_;
v_isShared_3741_ = v_isSharedCheck_3751_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___y_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3751_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
if (lean_obj_tag(v_a_3738_) == 1)
{
lean_del_object(v___x_3740_);
lean_del_object(v___x_3723_);
lean_dec_ref(v_e_3692_);
v___y_3728_ = v_a_3738_;
goto v___jp_3727_;
}
else
{
if (v___x_3735_ == 0)
{
lean_del_object(v___x_3719_);
if (lean_obj_tag(v_a_3738_) == 0)
{
uint8_t v_done_3742_; 
v_done_3742_ = lean_ctor_get_uint8(v_a_3738_, 0);
if (v_done_3742_ == 1)
{
uint8_t v_contextDependent_3743_; 
v_contextDependent_3743_ = lean_ctor_get_uint8(v_a_3738_, 1);
if (v_contextDependent_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_dec_ref(v_e_3692_);
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_a_3738_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 1, v___x_3726_);
lean_ctor_set(v___x_3723_, 0, v___x_3744_);
v___x_3746_ = v___x_3723_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3726_);
v___x_3746_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3746_);
v___x_3748_ = v___x_3740_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
else
{
lean_dec_ref(v_a_3738_);
lean_del_object(v___x_3740_);
lean_del_object(v___x_3723_);
v_a_3708_ = v___x_3734_;
goto v___jp_3707_;
}
}
else
{
lean_dec_ref(v_a_3738_);
lean_del_object(v___x_3740_);
lean_del_object(v___x_3723_);
v_a_3708_ = v___x_3734_;
goto v___jp_3707_;
}
}
else
{
lean_del_object(v___x_3740_);
lean_dec(v_a_3738_);
lean_del_object(v___x_3723_);
v_a_3708_ = v___x_3734_;
goto v___jp_3707_;
}
}
else
{
lean_del_object(v___x_3740_);
lean_del_object(v___x_3723_);
lean_dec_ref(v_e_3692_);
v___y_3728_ = v_a_3738_;
goto v___jp_3727_;
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_del_object(v___x_3723_);
lean_del_object(v___x_3719_);
lean_dec_ref(v_e_3692_);
v_a_3752_ = lean_ctor_get(v___y_3737_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___y_3737_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___y_3737_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___y_3737_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
}
}
v___jp_3707_:
{
size_t v___x_3709_; size_t v___x_3710_; 
v___x_3709_ = ((size_t)1ULL);
v___x_3710_ = lean_usize_add(v_i_3695_, v___x_3709_);
lean_inc_ref(v_a_3708_);
v_i_3695_ = v___x_3710_;
v_b_3696_ = v_a_3708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object* v_erased_3860_, lean_object* v_e_3861_, lean_object* v_as_3862_, lean_object* v_sz_3863_, lean_object* v_i_3864_, lean_object* v_b_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
size_t v_sz_boxed_3876_; size_t v_i_boxed_3877_; lean_object* v_res_3878_; 
v_sz_boxed_3876_ = lean_unbox_usize(v_sz_3863_);
lean_dec(v_sz_3863_);
v_i_boxed_3877_ = lean_unbox_usize(v_i_3864_);
lean_dec(v_i_3864_);
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3860_, v_e_3861_, v_as_3862_, v_sz_boxed_3876_, v_i_boxed_3877_, v_b_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v_as_3862_);
lean_dec_ref(v_erased_3860_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object* v_tree_3881_, lean_object* v_erased_3882_, lean_object* v_e_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_candidates_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v_candidates_3894_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_tree_3881_, v_e_3883_);
v___x_3895_ = lean_array_get_size(v_candidates_3894_);
v___x_3896_ = lean_unsigned_to_nat(0u);
v___x_3897_ = lean_nat_dec_eq(v___x_3895_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; size_t v_sz_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v___x_3898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v_sz_3899_ = lean_array_size(v_candidates_3894_);
v___x_3900_ = ((size_t)0ULL);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3882_, v_e_3883_, v_candidates_3894_, v_sz_3899_, v___x_3900_, v___x_3898_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
lean_dec_ref(v_candidates_3894_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3915_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3915_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3915_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_fst_3906_; 
v_fst_3906_ = lean_ctor_get(v_a_3902_, 0);
lean_inc(v_fst_3906_);
lean_dec(v_a_3902_);
if (lean_obj_tag(v_fst_3906_) == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3907_, 0, v___x_3897_);
lean_ctor_set_uint8(v___x_3907_, 1, v___x_3897_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3907_);
v___x_3909_ = v___x_3904_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
else
{
lean_object* v_val_3911_; lean_object* v___x_3913_; 
v_val_3911_ = lean_ctor_get(v_fst_3906_, 0);
lean_inc(v_val_3911_);
lean_dec_ref(v_fst_3906_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v_val_3911_);
v___x_3913_ = v___x_3904_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_val_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
v_a_3916_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3901_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3901_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec_ref(v_candidates_3894_);
lean_dec_ref(v_e_3883_);
v___x_3924_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0));
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object* v_tree_3926_, lean_object* v_erased_3927_, lean_object* v_e_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_3926_, v_erased_3927_, v_e_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_erased_3927_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object* v_00_u03b1_3940_, lean_object* v_x_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_x_3941_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3953_, lean_object* v_x_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_00_u03b1_3953_, v_x_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object* v_oldTraces_3966_, lean_object* v_data_3967_, lean_object* v_ref_3968_, lean_object* v_msg_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_oldTraces_3966_, v_data_3967_, v_ref_3968_, v_msg_3969_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object* v_oldTraces_3981_, lean_object* v_data_3982_, lean_object* v_ref_3983_, lean_object* v_msg_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(v_oldTraces_3981_, v_data_3982_, v_ref_3983_, v_msg_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
return v_res_3995_;
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
