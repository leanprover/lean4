// Lean compiler output
// Module: Lean.Meta.AbstractNestedProofs
// Imports: public import Init.Grind.Util public import Lean.Meta.Closure public import Lean.Meta.Transform
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__0;
static lean_once_cell_t l_Lean_Meta_abstractNestedProofs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractNestedProofs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractProof___redArg___lam__0(lean_object* v_proof_1_, uint8_t v___x_2_, lean_object* v_inst_3_, uint8_t v_cache_4_, lean_object* v_type_5_){
_start:
{
uint8_t v___y_7_; 
if (v_cache_4_ == 0)
{
v___y_7_ = v_cache_4_;
goto v___jp_6_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = l_Lean_Expr_hasSorry(v_proof_1_);
if (v___x_13_ == 0)
{
v___y_7_ = v_cache_4_;
goto v___jp_6_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = 0;
v___y_7_ = v___x_14_;
goto v___jp_6_;
}
}
v___jp_6_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_box(v___x_2_);
v___x_10_ = lean_box(v___y_7_);
v___x_11_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxTheorem___boxed), 10, 5);
lean_closure_set(v___x_11_, 0, v_type_5_);
lean_closure_set(v___x_11_, 1, v_proof_1_);
lean_closure_set(v___x_11_, 2, v___x_9_);
lean_closure_set(v___x_11_, 3, v___x_8_);
lean_closure_set(v___x_11_, 4, v___x_10_);
v___x_12_ = lean_apply_2(v_inst_3_, lean_box(0), v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_1_ = stack[0].m_obj;
uint8_t v___x_2_ = stack[1].m_num;
lean_object* v_inst_3_ = stack[2].m_obj;
uint8_t v_cache_4_ = stack[3].m_num;
lean_object* v_type_5_ = stack[4].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Meta_abstractProof___redArg___lam__0(v_proof_1_, v___x_2_, v_inst_3_, v_cache_4_, v_type_5_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0___boxed(lean_object* v_proof_16_, lean_object* v___x_17_, lean_object* v_inst_18_, lean_object* v_cache_19_, lean_object* v_type_20_){
_start:
{
uint8_t v___x_151__boxed_21_; uint8_t v_cache_boxed_22_; lean_object* v_res_23_; 
v___x_151__boxed_21_ = lean_unbox(v___x_17_);
v_cache_boxed_22_ = lean_unbox(v_cache_19_);
v_res_23_ = l_Lean_Meta_abstractProof___redArg___lam__0(v_proof_16_, v___x_151__boxed_21_, v_inst_18_, v_cache_boxed_22_, v_type_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__1(lean_object* v_postprocessType_24_, lean_object* v_toBind_25_, lean_object* v___f_26_, lean_object* v_type_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_apply_1(v_postprocessType_24_, v_type_27_);
v___x_29_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v___x_28_, v___f_26_);
return v___x_29_;
}
}
lean_object* l_Lean_Meta_abstractProof___redArg___lam__2(uint8_t v___x_30_, lean_object* v_inst_31_, lean_object* v_toBind_32_, lean_object* v___f_33_, lean_object* v_type_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = lean_box(v___x_30_);
v___x_36_ = lean_box(v___x_30_);
v___x_37_ = lean_box(v___x_30_);
v___x_38_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___boxed), 9, 4);
lean_closure_set(v___x_38_, 0, v_type_34_);
lean_closure_set(v___x_38_, 1, v___x_35_);
lean_closure_set(v___x_38_, 2, v___x_36_);
lean_closure_set(v___x_38_, 3, v___x_37_);
v___x_39_ = lean_apply_2(v_inst_31_, lean_box(0), v___x_38_);
v___x_40_ = lean_apply_4(v_toBind_32_, lean_box(0), lean_box(0), v___x_39_, v___f_33_);
return v___x_40_;
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_30_ = stack[0].m_num;
lean_object* v_inst_31_ = stack[1].m_obj;
lean_object* v_toBind_32_ = stack[2].m_obj;
lean_object* v___f_33_ = stack[3].m_obj;
lean_object* v_type_34_ = stack[4].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_Lean_Meta_abstractProof___redArg___lam__2(v___x_30_, v_inst_31_, v_toBind_32_, v___f_33_, v_type_34_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2___boxed(lean_object* v___x_42_, lean_object* v_inst_43_, lean_object* v_toBind_44_, lean_object* v___f_45_, lean_object* v_type_46_){
_start:
{
uint8_t v___x_197__boxed_47_; lean_object* v_res_48_; 
v___x_197__boxed_47_ = lean_unbox(v___x_42_);
v_res_48_ = l_Lean_Meta_abstractProof___redArg___lam__2(v___x_197__boxed_47_, v_inst_43_, v_toBind_44_, v___f_45_, v_type_46_);
return v_res_48_;
}
}
lean_object* l_Lean_Meta_abstractProof___redArg___lam__3(lean_object* v_type_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Core_betaReduce(v_type_49_, v___y_52_, v___y_53_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_49_ = stack[0].m_obj;
lean_object* v___y_50_ = stack[1].m_obj;
lean_object* v___y_51_ = stack[2].m_obj;
lean_object* v___y_52_ = stack[3].m_obj;
lean_object* v___y_53_ = stack[4].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_Lean_Meta_abstractProof___redArg___lam__3(v_type_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3___boxed(lean_object* v_type_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_abstractProof___redArg___lam__3(v_type_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__4(lean_object* v_inst_64_, lean_object* v_toBind_65_, lean_object* v___f_66_, lean_object* v_type_67_){
_start:
{
lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___f_68_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__3___boxed), 6, 1);
lean_closure_set(v___f_68_, 0, v_type_67_);
v___x_69_ = lean_apply_2(v_inst_64_, lean_box(0), v___f_68_);
v___x_70_ = lean_apply_4(v_toBind_65_, lean_box(0), lean_box(0), v___x_69_, v___f_66_);
return v___x_70_;
}
}
lean_object* l_Lean_Meta_abstractProof___redArg(lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_proof_75_, uint8_t v_cache_76_, lean_object* v_postprocessType_77_){
_start:
{
lean_object* v_toBind_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_toBind_78_ = lean_ctor_get(v_inst_71_, 1);
lean_inc_n(v_toBind_78_, 4);
lean_inc_ref(v_proof_75_);
v___x_79_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_79_, 0, v_proof_75_);
lean_inc_n(v_inst_72_, 3);
v___x_80_ = lean_apply_2(v_inst_72_, lean_box(0), v___x_79_);
v___x_81_ = 1;
v___x_82_ = lean_box(v___x_81_);
v___x_83_ = lean_box(v_cache_76_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_84_, 0, v_proof_75_);
lean_closure_set(v___f_84_, 1, v___x_82_);
lean_closure_set(v___f_84_, 2, v_inst_72_);
lean_closure_set(v___f_84_, 3, v___x_83_);
v___f_85_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__1), 4, 3);
lean_closure_set(v___f_85_, 0, v_postprocessType_77_);
lean_closure_set(v___f_85_, 1, v_toBind_78_);
lean_closure_set(v___f_85_, 2, v___f_84_);
v___x_86_ = lean_box(v___x_81_);
v___f_87_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_87_, 0, v___x_86_);
lean_closure_set(v___f_87_, 1, v_inst_72_);
lean_closure_set(v___f_87_, 2, v_toBind_78_);
lean_closure_set(v___f_87_, 3, v___f_85_);
v___f_88_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__4), 4, 3);
lean_closure_set(v___f_88_, 0, v_inst_72_);
lean_closure_set(v___f_88_, 1, v_toBind_78_);
lean_closure_set(v___f_88_, 2, v___f_87_);
v___x_89_ = l_Lean_withoutExporting___redArg(v_inst_71_, v_inst_73_, v_inst_74_, v___x_80_, v___x_81_);
v___x_90_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_89_, v___f_88_);
return v___x_90_;
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_71_ = stack[0].m_obj;
lean_object* v_inst_72_ = stack[1].m_obj;
lean_object* v_inst_73_ = stack[2].m_obj;
lean_object* v_inst_74_ = stack[3].m_obj;
lean_object* v_proof_75_ = stack[4].m_obj;
uint8_t v_cache_76_ = stack[5].m_num;
lean_object* v_postprocessType_77_ = stack[6].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_Meta_abstractProof___redArg(v_inst_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_proof_75_, v_cache_76_, v_postprocessType_77_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___boxed(lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_proof_96_, lean_object* v_cache_97_, lean_object* v_postprocessType_98_){
_start:
{
uint8_t v_cache_boxed_99_; lean_object* v_res_100_; 
v_cache_boxed_99_ = lean_unbox(v_cache_97_);
v_res_100_ = l_Lean_Meta_abstractProof___redArg(v_inst_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_proof_96_, v_cache_boxed_99_, v_postprocessType_98_);
return v_res_100_;
}
}
lean_object* l_Lean_Meta_abstractProof(lean_object* v_m_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_proof_107_, uint8_t v_cache_108_, lean_object* v_postprocessType_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_abstractProof___redArg(v_inst_102_, v_inst_103_, v_inst_104_, v_inst_106_, v_proof_107_, v_cache_108_, v_postprocessType_109_);
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_102_ = stack[1].m_obj;
lean_object* v_inst_103_ = stack[2].m_obj;
lean_object* v_inst_104_ = stack[3].m_obj;
lean_object* v_inst_105_ = stack[4].m_obj;
lean_object* v_inst_106_ = stack[5].m_obj;
lean_object* v_proof_107_ = stack[6].m_obj;
uint8_t v_cache_108_ = stack[7].m_num;
lean_object* v_postprocessType_109_ = stack[8].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Meta_abstractProof(lean_box(0), v_inst_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_proof_107_, v_cache_108_, v_postprocessType_109_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___boxed(lean_object* v_m_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_proof_118_, lean_object* v_cache_119_, lean_object* v_postprocessType_120_){
_start:
{
uint8_t v_cache_boxed_121_; lean_object* v_res_122_; 
v_cache_boxed_121_ = lean_unbox(v_cache_119_);
v_res_122_ = l_Lean_Meta_abstractProof(v_m_112_, v_inst_113_, v_inst_114_, v_inst_115_, v_inst_116_, v_inst_117_, v_proof_118_, v_cache_boxed_121_, v_postprocessType_120_);
lean_dec_ref(v_inst_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody(lean_object* v_e_123_){
_start:
{
if (lean_obj_tag(v_e_123_) == 6)
{
lean_object* v_body_124_; 
v_body_124_ = lean_ctor_get(v_e_123_, 2);
v_e_123_ = v_body_124_;
goto _start;
}
else
{
lean_inc_ref(v_e_123_);
return v_e_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody___boxed(lean_object* v_e_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_126_);
lean_dec_ref(v_e_126_);
return v_res_127_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(uint8_t v_a_128_, uint8_t v___x_129_, lean_object* v_as_130_, size_t v_i_131_, size_t v_stop_132_){
_start:
{
uint8_t v___x_133_; 
v___x_133_ = lean_usize_dec_eq(v_i_131_, v_stop_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; uint8_t v___y_136_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_134_ = 1;
v___x_140_ = lean_array_uget_borrowed(v_as_130_, v_i_131_);
v___x_141_ = l_Lean_Expr_isAtomic(v___x_140_);
if (v___x_141_ == 0)
{
v___y_136_ = v_a_128_;
goto v___jp_135_;
}
else
{
v___y_136_ = v___x_129_;
goto v___jp_135_;
}
v___jp_135_:
{
if (v___y_136_ == 0)
{
size_t v___x_137_; size_t v___x_138_; 
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_add(v_i_131_, v___x_137_);
v_i_131_ = v___x_138_;
goto _start;
}
else
{
return v___x_134_;
}
}
}
else
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_128_ = stack[0].m_num;
uint8_t v___x_129_ = stack[1].m_num;
lean_object* v_as_130_ = stack[2].m_obj;
size_t v_i_131_ = stack[3].m_num;
size_t v_stop_132_ = stack[4].m_num;
uint8_t v_res_143_;
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_128_, v___x_129_, v_as_130_, v_i_131_, v_stop_132_);
stack->m_num = v_res_143_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object* v_a_144_, lean_object* v___x_145_, lean_object* v_as_146_, lean_object* v_i_147_, lean_object* v_stop_148_){
_start:
{
uint8_t v_a_4103__boxed_149_; uint8_t v___x_4104__boxed_150_; size_t v_i_boxed_151_; size_t v_stop_boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v_a_4103__boxed_149_ = lean_unbox(v_a_144_);
v___x_4104__boxed_150_ = lean_unbox(v___x_145_);
v_i_boxed_151_ = lean_unbox_usize(v_i_147_);
lean_dec(v_i_147_);
v_stop_boxed_152_ = lean_unbox_usize(v_stop_148_);
lean_dec(v_stop_148_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4103__boxed_149_, v___x_4104__boxed_150_, v_as_146_, v_i_boxed_151_, v_stop_boxed_152_);
lean_dec_ref(v_as_146_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(uint8_t v_a_155_, uint8_t v___x_156_, lean_object* v___x_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_158_) == 5)
{
lean_object* v_fn_175_; lean_object* v_arg_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_fn_175_ = lean_ctor_get(v_x_158_, 0);
lean_inc_ref(v_fn_175_);
v_arg_176_ = lean_ctor_get(v_x_158_, 1);
lean_inc_ref(v_arg_176_);
lean_dec_ref_known(v_x_158_, 2);
v___x_177_ = lean_array_set(v_x_159_, v_x_160_, v_arg_176_);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_sub(v_x_160_, v___x_178_);
lean_dec(v_x_160_);
v_x_158_ = v_fn_175_;
v_x_159_ = v___x_177_;
v_x_160_ = v___x_179_;
goto _start;
}
else
{
uint8_t v___x_181_; 
lean_dec(v_x_160_);
v___x_181_ = l_Lean_Expr_isAtomic(v_x_158_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref(v_x_159_);
lean_dec_ref(v_x_158_);
lean_dec_ref(v___x_157_);
v___x_182_ = lean_box(v_a_155_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
else
{
if (v___x_156_ == 0)
{
if (lean_obj_tag(v_x_158_) == 4)
{
lean_object* v_declName_184_; uint8_t v___x_185_; 
v_declName_184_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_declName_184_);
lean_dec_ref_known(v_x_158_, 2);
v___x_185_ = l_Lean_Environment_contains(v___x_157_, v_declName_184_, v_a_155_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec_ref(v_x_159_);
v___x_186_ = lean_box(v_a_155_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
else
{
goto v___jp_162_;
}
}
else
{
lean_dec_ref(v_x_158_);
lean_dec_ref(v___x_157_);
goto v___jp_162_;
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec_ref(v_x_159_);
lean_dec_ref(v_x_158_);
lean_dec_ref(v___x_157_);
v___x_188_ = lean_box(v_a_155_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
}
v___jp_162_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_array_get_size(v_x_159_);
v___x_165_ = lean_nat_dec_lt(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec_ref(v_x_159_);
v___x_166_ = lean_box(v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
else
{
if (v___x_165_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec_ref(v_x_159_);
v___x_168_ = lean_box(v___x_165_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
else
{
size_t v___x_170_; size_t v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = ((size_t)0ULL);
v___x_171_ = lean_usize_of_nat(v___x_164_);
v___x_172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_155_, v___x_156_, v_x_159_, v___x_170_, v___x_171_);
lean_dec_ref(v_x_159_);
v___x_173_ = lean_box(v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_155_ = stack[0].m_num;
uint8_t v___x_156_ = stack[1].m_num;
lean_object* v___x_157_ = stack[2].m_obj;
lean_object* v_x_158_ = stack[3].m_obj;
lean_object* v_x_159_ = stack[4].m_obj;
lean_object* v_x_160_ = stack[5].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_155_, v___x_156_, v___x_157_, v_x_158_, v_x_159_, v_x_160_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg___boxed(lean_object* v_a_191_, lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v___y_197_){
_start:
{
uint8_t v_a_4143__boxed_198_; uint8_t v___x_4144__boxed_199_; lean_object* v_res_200_; 
v_a_4143__boxed_198_ = lean_unbox(v_a_191_);
v___x_4144__boxed_199_ = lean_unbox(v___x_192_);
v_res_200_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_4143__boxed_198_, v___x_4144__boxed_199_, v___x_193_, v_x_194_, v_x_195_, v_x_196_);
return v_res_200_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_201_, uint8_t v___x_202_, lean_object* v___x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
if (lean_obj_tag(v_x_204_) == 5)
{
lean_object* v_fn_225_; lean_object* v_arg_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_fn_225_ = lean_ctor_get(v_x_204_, 0);
lean_inc_ref(v_fn_225_);
v_arg_226_ = lean_ctor_get(v_x_204_, 1);
lean_inc_ref(v_arg_226_);
lean_dec_ref_known(v_x_204_, 2);
v___x_227_ = lean_array_set(v_x_205_, v_x_206_, v_arg_226_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_sub(v_x_206_, v___x_228_);
v___x_230_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_201_, v___x_202_, v___x_203_, v_fn_225_, v___x_227_, v___x_229_);
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
v___x_231_ = l_Lean_Expr_isAtomic(v_x_204_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v_x_205_);
lean_dec_ref(v_x_204_);
lean_dec_ref(v___x_203_);
v___x_232_ = lean_box(v_a_201_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
else
{
if (v___x_202_ == 0)
{
if (lean_obj_tag(v_x_204_) == 4)
{
lean_object* v_declName_234_; uint8_t v___x_235_; 
v_declName_234_ = lean_ctor_get(v_x_204_, 0);
lean_inc(v_declName_234_);
lean_dec_ref_known(v_x_204_, 2);
v___x_235_ = l_Lean_Environment_contains(v___x_203_, v_declName_234_, v_a_201_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref(v_x_205_);
v___x_236_ = lean_box(v_a_201_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
else
{
goto v___jp_212_;
}
}
else
{
lean_dec_ref(v_x_204_);
lean_dec_ref(v___x_203_);
goto v___jp_212_;
}
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_x_205_);
lean_dec_ref(v_x_204_);
lean_dec_ref(v___x_203_);
v___x_238_ = lean_box(v_a_201_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
v___jp_212_:
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_array_get_size(v_x_205_);
v___x_215_ = lean_nat_dec_lt(v___x_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v_x_205_);
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
else
{
if (v___x_215_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec_ref(v_x_205_);
v___x_218_ = lean_box(v___x_215_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
else
{
size_t v___x_220_; size_t v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_220_ = ((size_t)0ULL);
v___x_221_ = lean_usize_of_nat(v___x_214_);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_201_, v___x_202_, v_x_205_, v___x_220_, v___x_221_);
lean_dec_ref(v_x_205_);
v___x_223_ = lean_box(v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_201_ = stack[0].m_num;
uint8_t v___x_202_ = stack[1].m_num;
lean_object* v___x_203_ = stack[2].m_obj;
lean_object* v_x_204_ = stack[3].m_obj;
lean_object* v_x_205_ = stack[4].m_obj;
lean_object* v_x_206_ = stack[5].m_obj;
lean_object* v___y_207_ = stack[6].m_obj;
lean_object* v___y_208_ = stack[7].m_obj;
lean_object* v___y_209_ = stack[8].m_obj;
lean_object* v___y_210_ = stack[9].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_201_, v___x_202_, v___x_203_, v_x_204_, v_x_205_, v_x_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_241_, lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
uint8_t v_a_4263__boxed_252_; uint8_t v___x_4264__boxed_253_; lean_object* v_res_254_; 
v_a_4263__boxed_252_ = lean_unbox(v_a_241_);
v___x_4264__boxed_253_ = lean_unbox(v___x_242_);
v_res_254_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4263__boxed_252_, v___x_4264__boxed_253_, v___x_243_, v_x_244_, v_x_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v_x_246_);
return v_res_254_;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_262_; lean_object* v_dummy_263_; 
v___x_262_ = lean_box(0);
v_dummy_263_ = l_Lean_Expr_sort___override(v___x_262_);
return v_dummy_263_;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object* v_e_264_, lean_object* v_env_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
lean_inc_ref(v_e_264_);
v___x_271_ = l_Lean_Meta_isProof(v_e_264_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; uint8_t v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v___x_273_ = lean_unbox(v_a_272_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_env_265_);
lean_dec_ref(v_e_264_);
return v___x_271_;
}
else
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_292_; 
lean_inc(v_a_272_);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v___x_271_, 0);
lean_dec(v_unused_293_);
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_292_;
goto v_resetjp_274_;
}
else
{
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_292_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3));
v___x_278_ = l_Lean_Expr_isAppOf(v_e_264_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v_dummy_280_; lean_object* v_nargs_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; 
lean_del_object(v___x_275_);
v___x_279_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_264_);
lean_dec_ref(v_e_264_);
v_dummy_280_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_281_ = l_Lean_Expr_getAppNumArgs(v___x_279_);
lean_inc(v_nargs_281_);
v___x_282_ = lean_mk_array(v_nargs_281_, v_dummy_280_);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_sub(v_nargs_281_, v___x_283_);
lean_dec(v_nargs_281_);
v___x_285_ = lean_unbox(v_a_272_);
lean_dec(v_a_272_);
v___x_286_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v___x_285_, v___x_278_, v_env_265_, v___x_279_, v___x_282_, v___x_284_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___x_284_);
return v___x_286_;
}
else
{
uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
lean_dec(v_a_272_);
lean_dec_ref(v_env_265_);
lean_dec_ref(v_e_264_);
v___x_287_ = 0;
v___x_288_ = lean_box(v___x_287_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_288_);
v___x_290_ = v___x_275_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_265_);
lean_dec_ref(v_e_264_);
return v___x_271_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_264_ = stack[0].m_obj;
lean_object* v_env_265_ = stack[1].m_obj;
lean_object* v___y_266_ = stack[2].m_obj;
lean_object* v___y_267_ = stack[3].m_obj;
lean_object* v___y_268_ = stack[4].m_obj;
lean_object* v___y_269_ = stack[5].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_264_, v_env_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object* v_e_295_, lean_object* v_env_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_295_, v_env_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(lean_object* v___y_303_, uint8_t v_isExporting_304_, lean_object* v___x_305_, lean_object* v___y_306_, lean_object* v___x_307_, lean_object* v_a_x3f_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_env_311_; lean_object* v_nextMacroScope_312_; lean_object* v_ngen_313_; lean_object* v_auxDeclNGen_314_; lean_object* v_traceState_315_; lean_object* v_recordedDeps_316_; lean_object* v_messages_317_; lean_object* v_infoState_318_; lean_object* v_snapshotTasks_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_344_; 
v___x_310_ = lean_st_ref_take(v___y_303_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
v_nextMacroScope_312_ = lean_ctor_get(v___x_310_, 1);
v_ngen_313_ = lean_ctor_get(v___x_310_, 2);
v_auxDeclNGen_314_ = lean_ctor_get(v___x_310_, 3);
v_traceState_315_ = lean_ctor_get(v___x_310_, 4);
v_recordedDeps_316_ = lean_ctor_get(v___x_310_, 6);
v_messages_317_ = lean_ctor_get(v___x_310_, 7);
v_infoState_318_ = lean_ctor_get(v___x_310_, 8);
v_snapshotTasks_319_ = lean_ctor_get(v___x_310_, 9);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v___x_310_, 5);
lean_dec(v_unused_345_);
v___x_321_ = v___x_310_;
v_isShared_322_ = v_isSharedCheck_344_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_snapshotTasks_319_);
lean_inc(v_infoState_318_);
lean_inc(v_messages_317_);
lean_inc(v_recordedDeps_316_);
lean_inc(v_traceState_315_);
lean_inc(v_auxDeclNGen_314_);
lean_inc(v_ngen_313_);
lean_inc(v_nextMacroScope_312_);
lean_inc(v_env_311_);
lean_dec(v___x_310_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_344_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = l_Lean_Environment_setExporting(v_env_311_, v_isExporting_304_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 5, v___x_305_);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_nextMacroScope_312_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_ngen_313_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_auxDeclNGen_314_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_traceState_315_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_recordedDeps_316_);
lean_ctor_set(v_reuseFailAlloc_343_, 7, v_messages_317_);
lean_ctor_set(v_reuseFailAlloc_343_, 8, v_infoState_318_);
lean_ctor_set(v_reuseFailAlloc_343_, 9, v_snapshotTasks_319_);
v___x_325_ = v_reuseFailAlloc_343_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_mctx_328_; lean_object* v_zetaDeltaFVarIds_329_; lean_object* v_postponed_330_; lean_object* v_diag_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_341_; 
v___x_326_ = lean_st_ref_put(v___y_303_, v___x_325_);
v___x_327_ = lean_st_ref_take(v___y_306_);
v_mctx_328_ = lean_ctor_get(v___x_327_, 0);
v_zetaDeltaFVarIds_329_ = lean_ctor_get(v___x_327_, 2);
v_postponed_330_ = lean_ctor_get(v___x_327_, 3);
v_diag_331_ = lean_ctor_get(v___x_327_, 4);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v___x_327_, 1);
lean_dec(v_unused_342_);
v___x_333_ = v___x_327_;
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_diag_331_);
lean_inc(v_postponed_330_);
lean_inc(v_zetaDeltaFVarIds_329_);
lean_inc(v_mctx_328_);
lean_dec(v___x_327_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_box(0);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_307_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_mctx_328_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_zetaDeltaFVarIds_329_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_postponed_330_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_diag_331_);
v___x_337_ = v_reuseFailAlloc_340_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_st_ref_put(v___y_306_, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_335_);
return v___x_339_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_303_ = stack[0].m_obj;
uint8_t v_isExporting_304_ = stack[1].m_num;
lean_object* v___x_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v___x_307_ = stack[4].m_obj;
lean_object* v_a_x3f_308_ = stack[5].m_obj;
lean_object* v_res_346_;
v_res_346_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_303_, v_isExporting_304_, v___x_305_, v___y_306_, v___x_307_, v_a_x3f_308_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_347_, lean_object* v_isExporting_348_, lean_object* v___x_349_, lean_object* v___y_350_, lean_object* v___x_351_, lean_object* v_a_x3f_352_, lean_object* v___y_353_){
_start:
{
uint8_t v_isExporting_boxed_354_; lean_object* v_res_355_; 
v_isExporting_boxed_354_ = lean_unbox(v_isExporting_348_);
v_res_355_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_347_, v_isExporting_boxed_354_, v___x_349_, v___y_350_, v___x_351_, v_a_x3f_352_);
lean_dec(v_a_x3f_352_);
lean_dec(v___y_350_);
lean_dec(v___y_347_);
return v_res_355_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_356_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__1);
v___x_362_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
lean_ctor_set(v___x_362_, 3, v___x_361_);
lean_ctor_set(v___x_362_, 4, v___x_361_);
lean_ctor_set(v___x_362_, 5, v___x_361_);
return v___x_362_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(lean_object* v_x_363_, uint8_t v_isExporting_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v___x_372_; uint8_t v_isModule_373_; 
v___x_370_ = lean_st_ref_get(v___y_368_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v___x_372_ = l_Lean_Environment_header(v_env_371_);
v_isModule_373_ = lean_ctor_get_uint8(v___x_372_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_372_);
if (v_isModule_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v_env_371_);
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
v___x_374_ = lean_apply_5(v_x_363_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, lean_box(0));
return v___x_374_;
}
else
{
uint8_t v_isExporting_375_; 
v_isExporting_375_ = lean_ctor_get_uint8(v_env_371_, sizeof(void*)*13);
lean_dec_ref(v_env_371_);
if (v_isExporting_364_ == 0)
{
if (v_isExporting_375_ == 0)
{
lean_object* v___x_442_; 
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
v___x_442_ = lean_apply_5(v_x_363_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, lean_box(0));
return v___x_442_;
}
else
{
goto v___jp_376_;
}
}
else
{
if (v_isExporting_375_ == 0)
{
goto v___jp_376_;
}
else
{
lean_object* v___x_443_; 
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
v___x_443_ = lean_apply_5(v_x_363_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, lean_box(0));
return v___x_443_;
}
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_traceState_382_; lean_object* v_recordedDeps_383_; lean_object* v_messages_384_; lean_object* v_infoState_385_; lean_object* v_snapshotTasks_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_440_; 
v___x_377_ = lean_st_ref_take(v___y_368_);
v_env_378_ = lean_ctor_get(v___x_377_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_377_, 1);
v_ngen_380_ = lean_ctor_get(v___x_377_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_377_, 3);
v_traceState_382_ = lean_ctor_get(v___x_377_, 4);
v_recordedDeps_383_ = lean_ctor_get(v___x_377_, 6);
v_messages_384_ = lean_ctor_get(v___x_377_, 7);
v_infoState_385_ = lean_ctor_get(v___x_377_, 8);
v_snapshotTasks_386_ = lean_ctor_get(v___x_377_, 9);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_377_, 5);
lean_dec(v_unused_441_);
v___x_388_ = v___x_377_;
v_isShared_389_ = v_isSharedCheck_440_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snapshotTasks_386_);
lean_inc(v_infoState_385_);
lean_inc(v_messages_384_);
lean_inc(v_recordedDeps_383_);
lean_inc(v_traceState_382_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_377_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_440_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = l_Lean_Environment_setExporting(v_env_378_, v_isExporting_364_);
v___x_391_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 5, v___x_391_);
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_traceState_382_);
lean_ctor_set(v_reuseFailAlloc_439_, 5, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_439_, 6, v_recordedDeps_383_);
lean_ctor_set(v_reuseFailAlloc_439_, 7, v_messages_384_);
lean_ctor_set(v_reuseFailAlloc_439_, 8, v_infoState_385_);
lean_ctor_set(v_reuseFailAlloc_439_, 9, v_snapshotTasks_386_);
v___x_393_ = v_reuseFailAlloc_439_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_mctx_396_; lean_object* v_zetaDeltaFVarIds_397_; lean_object* v_postponed_398_; lean_object* v_diag_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_437_; 
v___x_394_ = lean_st_ref_put(v___y_368_, v___x_393_);
v___x_395_ = lean_st_ref_take(v___y_366_);
v_mctx_396_ = lean_ctor_get(v___x_395_, 0);
v_zetaDeltaFVarIds_397_ = lean_ctor_get(v___x_395_, 2);
v_postponed_398_ = lean_ctor_get(v___x_395_, 3);
v_diag_399_ = lean_ctor_get(v___x_395_, 4);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_395_, 1);
lean_dec(v_unused_438_);
v___x_401_ = v___x_395_;
v_isShared_402_ = v_isSharedCheck_437_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_diag_399_);
lean_inc(v_postponed_398_);
lean_inc(v_zetaDeltaFVarIds_397_);
lean_inc(v_mctx_396_);
lean_dec(v___x_395_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_437_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_mctx_396_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_zetaDeltaFVarIds_397_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_postponed_398_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_diag_399_);
v___x_405_ = v_reuseFailAlloc_436_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v_r_407_; 
v___x_406_ = lean_st_ref_put(v___y_366_, v___x_405_);
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
v_r_407_ = lean_apply_5(v_x_363_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, lean_box(0));
if (lean_obj_tag(v_r_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_424_; 
v_a_408_ = lean_ctor_get(v_r_407_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_r_407_);
if (v_isSharedCheck_424_ == 0)
{
v___x_410_ = v_r_407_;
v_isShared_411_ = v_isSharedCheck_424_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v_r_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_424_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
lean_inc(v_a_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 1);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_423_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v___x_414_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_368_, v_isExporting_375_, v___x_391_, v___y_366_, v___x_403_, v___x_413_);
lean_dec_ref(v___x_413_);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_414_, 0);
lean_dec(v_unused_422_);
v___x_416_ = v___x_414_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_414_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_408_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_408_);
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
else
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_425_ = lean_ctor_get(v_r_407_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v_r_407_, 1);
v___x_426_ = lean_box(0);
v___x_427_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_368_, v_isExporting_375_, v___x_391_, v___y_366_, v___x_403_, v___x_426_);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v___x_427_, 0);
lean_dec(v_unused_435_);
v___x_429_ = v___x_427_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_dec(v___x_427_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 1);
lean_ctor_set(v___x_429_, 0, v_a_425_);
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_425_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_363_ = stack[0].m_obj;
uint8_t v_isExporting_364_ = stack[1].m_num;
lean_object* v___y_365_ = stack[2].m_obj;
lean_object* v___y_366_ = stack[3].m_obj;
lean_object* v___y_367_ = stack[4].m_obj;
lean_object* v___y_368_ = stack[5].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_363_, v_isExporting_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_445_, lean_object* v_isExporting_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v_isExporting_boxed_452_; lean_object* v_res_453_; 
v_isExporting_boxed_452_ = lean_unbox(v_isExporting_446_);
v_res_453_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_445_, v_isExporting_boxed_452_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_453_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_454_, uint8_t v_when_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
if (v_when_455_ == 0)
{
lean_object* v___x_461_; 
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
v___x_461_ = lean_apply_5(v_x_454_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, lean_box(0));
return v___x_461_;
}
else
{
uint8_t v___x_462_; lean_object* v___x_463_; 
v___x_462_ = 0;
v___x_463_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_454_, v___x_462_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_463_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_454_ = stack[0].m_obj;
uint8_t v_when_455_ = stack[1].m_num;
lean_object* v___y_456_ = stack[2].m_obj;
lean_object* v___y_457_ = stack[3].m_obj;
lean_object* v___y_458_ = stack[4].m_obj;
lean_object* v___y_459_ = stack[5].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_454_, v_when_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_465_, lean_object* v_when_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v_when_boxed_472_; lean_object* v_res_473_; 
v_when_boxed_472_ = lean_unbox(v_when_466_);
v_res_473_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_465_, v_when_boxed_472_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_473_;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v___f_482_; uint8_t v___x_483_; lean_object* v___x_484_; 
v___x_480_ = lean_st_ref_get(v_a_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_482_, 0, v_e_474_);
lean_closure_set(v___f_482_, 1, v_env_481_);
v___x_483_ = 1;
v___x_484_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_482_, v___x_483_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_484_;
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_474_ = stack[0].m_obj;
lean_object* v_a_475_ = stack[1].m_obj;
lean_object* v_a_476_ = stack[2].m_obj;
lean_object* v_a_477_ = stack[3].m_obj;
lean_object* v_a_478_ = stack[4].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_492_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(lean_object* v_00_u03b1_493_, lean_object* v_x_494_, uint8_t v_isExporting_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg(v_x_494_, v_isExporting_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_494_ = stack[1].m_obj;
uint8_t v_isExporting_495_ = stack[2].m_num;
lean_object* v___y_496_ = stack[3].m_obj;
lean_object* v___y_497_ = stack[4].m_obj;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(lean_box(0), v_x_494_, v_isExporting_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_503_, lean_object* v_x_504_, lean_object* v_isExporting_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v_isExporting_boxed_511_; lean_object* v_res_512_; 
v_isExporting_boxed_511_ = lean_unbox(v_isExporting_505_);
v_res_512_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3(v_00_u03b1_503_, v_x_504_, v_isExporting_boxed_511_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_512_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_513_, lean_object* v_x_514_, uint8_t v_when_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_514_, v_when_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v___x_521_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_514_ = stack[1].m_obj;
uint8_t v_when_515_ = stack[2].m_num;
lean_object* v___y_516_ = stack[3].m_obj;
lean_object* v___y_517_ = stack[4].m_obj;
lean_object* v___y_518_ = stack[5].m_obj;
lean_object* v___y_519_ = stack[6].m_obj;
lean_object* v_res_522_;
v_res_522_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_box(0), v_x_514_, v_when_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_523_, lean_object* v_x_524_, lean_object* v_when_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
uint8_t v_when_boxed_531_; lean_object* v_res_532_; 
v_when_boxed_531_ = lean_unbox(v_when_525_);
v_res_532_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_523_, v_x_524_, v_when_boxed_531_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_532_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(uint8_t v_a_533_, uint8_t v___x_534_, lean_object* v___x_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___redArg(v_a_533_, v___x_534_, v___x_535_, v_x_536_, v_x_537_, v_x_538_);
return v___x_544_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_533_ = stack[0].m_num;
uint8_t v___x_534_ = stack[1].m_num;
lean_object* v___x_535_ = stack[2].m_obj;
lean_object* v_x_536_ = stack[3].m_obj;
lean_object* v_x_537_ = stack[4].m_obj;
lean_object* v_x_538_ = stack[5].m_obj;
lean_object* v___y_539_ = stack[6].m_obj;
lean_object* v___y_540_ = stack[7].m_obj;
lean_object* v___y_541_ = stack[8].m_obj;
lean_object* v___y_542_ = stack[9].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(v_a_533_, v___x_534_, v___x_535_, v_x_536_, v_x_537_, v_x_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1___boxed(lean_object* v_a_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v_a_4965__boxed_557_; uint8_t v___x_4966__boxed_558_; lean_object* v_res_559_; 
v_a_4965__boxed_557_ = lean_unbox(v_a_546_);
v___x_4966__boxed_558_ = lean_unbox(v___x_547_);
v_res_559_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1_spec__1(v_a_4965__boxed_557_, v___x_4966__boxed_558_, v___x_548_, v_x_549_, v_x_550_, v_x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_559_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object* v_x_560_, uint8_t v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(v___y_561_);
lean_inc(v___y_562_);
v___x_569_ = lean_apply_7(v_x_560_, v___x_568_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, lean_box(0));
return v___x_569_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_560_ = stack[0].m_obj;
uint8_t v___y_561_ = stack[1].m_num;
lean_object* v___y_562_ = stack[2].m_obj;
lean_object* v___y_563_ = stack[3].m_obj;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v___y_565_ = stack[5].m_obj;
lean_object* v___y_566_ = stack[6].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(v_x_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object* v_x_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v___y_26151__boxed_579_; lean_object* v_res_580_; 
v___y_26151__boxed_579_ = lean_unbox(v___y_572_);
v_res_580_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(v_x_571_, v___y_26151__boxed_579_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_573_);
return v_res_580_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_lctx_581_, lean_object* v_localInsts_582_, lean_object* v_x_583_, uint8_t v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___x_593_; 
v___x_591_ = lean_box(v___y_584_);
lean_inc(v___y_585_);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_592_, 0, v_x_583_);
lean_closure_set(v___f_592_, 1, v___x_591_);
lean_closure_set(v___f_592_, 2, v___y_585_);
v___x_593_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_581_, v_localInsts_582_, v___f_592_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_593_) == 0)
{
return v___x_593_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_581_ = stack[0].m_obj;
lean_object* v_localInsts_582_ = stack[1].m_obj;
lean_object* v_x_583_ = stack[2].m_obj;
uint8_t v___y_584_ = stack[3].m_num;
lean_object* v___y_585_ = stack[4].m_obj;
lean_object* v___y_586_ = stack[5].m_obj;
lean_object* v___y_587_ = stack[6].m_obj;
lean_object* v___y_588_ = stack[7].m_obj;
lean_object* v___y_589_ = stack[8].m_obj;
lean_object* v_res_602_;
v_res_602_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_581_, v_localInsts_582_, v_x_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object* v_lctx_603_, lean_object* v_localInsts_604_, lean_object* v_x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
uint8_t v___y_26192__boxed_613_; lean_object* v_res_614_; 
v___y_26192__boxed_613_ = lean_unbox(v___y_606_);
v_res_614_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_603_, v_localInsts_604_, v_x_605_, v___y_26192__boxed_613_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
return v_res_614_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b1_615_, lean_object* v_lctx_616_, lean_object* v_localInsts_617_, lean_object* v_x_618_, uint8_t v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_616_, v_localInsts_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v___x_626_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_616_ = stack[1].m_obj;
lean_object* v_localInsts_617_ = stack[2].m_obj;
lean_object* v_x_618_ = stack[3].m_obj;
uint8_t v___y_619_ = stack[4].m_num;
lean_object* v___y_620_ = stack[5].m_obj;
lean_object* v___y_621_ = stack[6].m_obj;
lean_object* v___y_622_ = stack[7].m_obj;
lean_object* v___y_623_ = stack[8].m_obj;
lean_object* v___y_624_ = stack[9].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_box(0), v_lctx_616_, v_localInsts_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_00_u03b1_628_, lean_object* v_lctx_629_, lean_object* v_localInsts_630_, lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___y_26261__boxed_639_; lean_object* v_res_640_; 
v___y_26261__boxed_639_ = lean_unbox(v___y_632_);
v_res_640_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_00_u03b1_628_, v_lctx_629_, v_localInsts_630_, v_x_631_, v___y_26261__boxed_639_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
return v_res_640_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(lean_object* v_k_641_, uint8_t v___y_642_, lean_object* v___y_643_, lean_object* v_b_644_, lean_object* v_c_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(v___y_642_);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_643_);
v___x_652_ = lean_apply_9(v_k_641_, v_b_644_, v_c_645_, v___x_651_, v___y_643_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, lean_box(0));
return v___x_652_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_641_ = stack[0].m_obj;
uint8_t v___y_642_ = stack[1].m_num;
lean_object* v___y_643_ = stack[2].m_obj;
lean_object* v_b_644_ = stack[3].m_obj;
lean_object* v_c_645_ = stack[4].m_obj;
lean_object* v___y_646_ = stack[5].m_obj;
lean_object* v___y_647_ = stack[6].m_obj;
lean_object* v___y_648_ = stack[7].m_obj;
lean_object* v___y_649_ = stack[8].m_obj;
lean_object* v_res_653_;
v_res_653_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_641_, v___y_642_, v___y_643_, v_b_644_, v_c_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_653_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed(lean_object* v_k_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v_b_657_, lean_object* v_c_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
uint8_t v___y_26299__boxed_664_; lean_object* v_res_665_; 
v___y_26299__boxed_664_ = lean_unbox(v___y_655_);
v_res_665_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0(v_k_654_, v___y_26299__boxed_664_, v___y_656_, v_b_657_, v_c_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_656_);
return v_res_665_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_e_666_, lean_object* v_k_667_, uint8_t v_cleanupAnnotations_668_, uint8_t v_preserveNondepLet_669_, uint8_t v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___f_678_; uint8_t v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = lean_box(v___y_670_);
lean_inc(v___y_671_);
v___f_678_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_678_, 0, v_k_667_);
lean_closure_set(v___f_678_, 1, v___x_677_);
lean_closure_set(v___f_678_, 2, v___y_671_);
v___x_679_ = 1;
v___x_680_ = 0;
v___x_681_ = lean_box(0);
v___x_682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_666_, v___x_679_, v___x_679_, v_preserveNondepLet_669_, v___x_680_, v___x_681_, v___f_678_, v_cleanupAnnotations_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_682_) == 0)
{
return v___x_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_666_ = stack[0].m_obj;
lean_object* v_k_667_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_668_ = stack[2].m_num;
uint8_t v_preserveNondepLet_669_ = stack[3].m_num;
uint8_t v___y_670_ = stack[4].m_num;
lean_object* v___y_671_ = stack[5].m_obj;
lean_object* v___y_672_ = stack[6].m_obj;
lean_object* v___y_673_ = stack[7].m_obj;
lean_object* v___y_674_ = stack[8].m_obj;
lean_object* v___y_675_ = stack[9].m_obj;
lean_object* v_res_691_;
v_res_691_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_666_, v_k_667_, v_cleanupAnnotations_668_, v_preserveNondepLet_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_e_692_, lean_object* v_k_693_, lean_object* v_cleanupAnnotations_694_, lean_object* v_preserveNondepLet_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_703_; uint8_t v_preserveNondepLet_boxed_704_; uint8_t v___y_26340__boxed_705_; lean_object* v_res_706_; 
v_cleanupAnnotations_boxed_703_ = lean_unbox(v_cleanupAnnotations_694_);
v_preserveNondepLet_boxed_704_ = lean_unbox(v_preserveNondepLet_695_);
v___y_26340__boxed_705_ = lean_unbox(v___y_696_);
v_res_706_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_692_, v_k_693_, v_cleanupAnnotations_boxed_703_, v_preserveNondepLet_boxed_704_, v___y_26340__boxed_705_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
return v_res_706_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_707_, lean_object* v_e_708_, lean_object* v_k_709_, uint8_t v_cleanupAnnotations_710_, uint8_t v_preserveNondepLet_711_, uint8_t v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_708_, v_k_709_, v_cleanupAnnotations_710_, v_preserveNondepLet_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_708_ = stack[1].m_obj;
lean_object* v_k_709_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_710_ = stack[3].m_num;
uint8_t v_preserveNondepLet_711_ = stack[4].m_num;
uint8_t v___y_712_ = stack[5].m_num;
lean_object* v___y_713_ = stack[6].m_obj;
lean_object* v___y_714_ = stack[7].m_obj;
lean_object* v___y_715_ = stack[8].m_obj;
lean_object* v___y_716_ = stack[9].m_obj;
lean_object* v___y_717_ = stack[10].m_obj;
lean_object* v_res_720_;
v_res_720_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_box(0), v_e_708_, v_k_709_, v_cleanupAnnotations_710_, v_preserveNondepLet_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_721_, lean_object* v_e_722_, lean_object* v_k_723_, lean_object* v_cleanupAnnotations_724_, lean_object* v_preserveNondepLet_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_733_; uint8_t v_preserveNondepLet_boxed_734_; uint8_t v___y_26418__boxed_735_; lean_object* v_res_736_; 
v_cleanupAnnotations_boxed_733_ = lean_unbox(v_cleanupAnnotations_724_);
v_preserveNondepLet_boxed_734_ = lean_unbox(v_preserveNondepLet_725_);
v___y_26418__boxed_735_ = lean_unbox(v___y_726_);
v_res_736_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_721_, v_e_722_, v_k_723_, v_cleanupAnnotations_boxed_733_, v_preserveNondepLet_boxed_734_, v___y_26418__boxed_735_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
return v_res_736_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(lean_object* v_type_737_, lean_object* v_k_738_, uint8_t v_cleanupAnnotations_739_, uint8_t v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___f_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_747_ = lean_box(v___y_740_);
lean_inc(v___y_741_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_748_, 0, v_k_738_);
lean_closure_set(v___f_748_, 1, v___x_747_);
lean_closure_set(v___f_748_, 2, v___y_741_);
v___x_749_ = 0;
v___x_750_ = lean_box(0);
v___x_751_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_749_, v___x_750_, v_type_737_, v___f_748_, v_cleanupAnnotations_739_, v___x_749_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_751_) == 0)
{
return v___x_751_;
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_737_ = stack[0].m_obj;
lean_object* v_k_738_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_739_ = stack[2].m_num;
uint8_t v___y_740_ = stack[3].m_num;
lean_object* v___y_741_ = stack[4].m_obj;
lean_object* v___y_742_ = stack[5].m_obj;
lean_object* v___y_743_ = stack[6].m_obj;
lean_object* v___y_744_ = stack[7].m_obj;
lean_object* v___y_745_ = stack[8].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_737_, v_k_738_, v_cleanupAnnotations_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg___boxed(lean_object* v_type_761_, lean_object* v_k_762_, lean_object* v_cleanupAnnotations_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_771_; uint8_t v___y_26456__boxed_772_; lean_object* v_res_773_; 
v_cleanupAnnotations_boxed_771_ = lean_unbox(v_cleanupAnnotations_763_);
v___y_26456__boxed_772_ = lean_unbox(v___y_764_);
v_res_773_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_761_, v_k_762_, v_cleanupAnnotations_boxed_771_, v___y_26456__boxed_772_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
return v_res_773_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_00_u03b1_774_, lean_object* v_type_775_, lean_object* v_k_776_, uint8_t v_cleanupAnnotations_777_, uint8_t v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_type_775_, v_k_776_, v_cleanupAnnotations_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_785_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_775_ = stack[1].m_obj;
lean_object* v_k_776_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_777_ = stack[3].m_num;
uint8_t v___y_778_ = stack[4].m_num;
lean_object* v___y_779_ = stack[5].m_obj;
lean_object* v___y_780_ = stack[6].m_obj;
lean_object* v___y_781_ = stack[7].m_obj;
lean_object* v___y_782_ = stack[8].m_obj;
lean_object* v___y_783_ = stack[9].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_box(0), v_type_775_, v_k_776_, v_cleanupAnnotations_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_00_u03b1_787_, lean_object* v_type_788_, lean_object* v_k_789_, lean_object* v_cleanupAnnotations_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_798_; uint8_t v___y_26531__boxed_799_; lean_object* v_res_800_; 
v_cleanupAnnotations_boxed_798_ = lean_unbox(v_cleanupAnnotations_790_);
v___y_26531__boxed_799_ = lean_unbox(v___y_791_);
v_res_800_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_00_u03b1_787_, v_type_788_, v_k_789_, v_cleanupAnnotations_boxed_798_, v___y_26531__boxed_799_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
lean_object* v_ks_805_; lean_object* v_vs_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_830_; 
v_ks_805_ = lean_ctor_get(v_x_801_, 0);
v_vs_806_ = lean_ctor_get(v_x_801_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_830_ == 0)
{
v___x_808_ = v_x_801_;
v_isShared_809_ = v_isSharedCheck_830_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_vs_806_);
lean_inc(v_ks_805_);
lean_dec(v_x_801_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_830_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = lean_array_get_size(v_ks_805_);
v___x_811_ = lean_nat_dec_lt(v_x_802_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec(v_x_802_);
v___x_812_ = lean_array_push(v_ks_805_, v_x_803_);
v___x_813_ = lean_array_push(v_vs_806_, v_x_804_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_813_);
lean_ctor_set(v___x_808_, 0, v___x_812_);
v___x_815_ = v___x_808_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_object* v_k_x27_817_; uint8_t v___x_818_; 
v_k_x27_817_ = lean_array_fget_borrowed(v_ks_805_, v_x_802_);
v___x_818_ = l_Lean_instBEqFVarId_beq(v_x_803_, v_k_x27_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_820_; 
if (v_isShared_809_ == 0)
{
v___x_820_ = v___x_808_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_ks_805_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_vs_806_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_x_802_, v___x_821_);
lean_dec(v_x_802_);
v_x_801_ = v___x_820_;
v_x_802_ = v___x_822_;
goto _start;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_825_ = lean_array_fset(v_ks_805_, v_x_802_, v_x_803_);
v___x_826_ = lean_array_fset(v_vs_806_, v_x_802_, v_x_804_);
lean_dec(v_x_802_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_826_);
lean_ctor_set(v___x_808_, 0, v___x_825_);
v___x_828_ = v___x_808_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object* v_n_831_, lean_object* v_k_832_, lean_object* v_v_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_n_831_, v___x_834_, v_k_832_, v_v_833_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_836_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_x_837_, size_t v_x_838_, size_t v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_837_) == 0)
{
lean_object* v_es_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v_j_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_es_842_ = lean_ctor_get(v_x_837_, 0);
v___x_843_ = ((size_t)31ULL);
v___x_844_ = lean_usize_land(v_x_838_, v___x_843_);
v_j_845_ = lean_usize_to_nat(v___x_844_);
v___x_846_ = lean_array_get_size(v_es_842_);
v___x_847_ = lean_nat_dec_lt(v_j_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_j_845_);
lean_dec(v_x_841_);
lean_dec(v_x_840_);
return v_x_837_;
}
else
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_886_; 
lean_inc_ref(v_es_842_);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_x_837_, 0);
lean_dec(v_unused_887_);
v___x_849_ = v_x_837_;
v_isShared_850_ = v_isSharedCheck_886_;
goto v_resetjp_848_;
}
else
{
lean_dec(v_x_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_886_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_v_851_; lean_object* v___x_852_; lean_object* v_xs_x27_853_; lean_object* v___y_855_; 
v_v_851_ = lean_array_fget(v_es_842_, v_j_845_);
v___x_852_ = lean_box(0);
v_xs_x27_853_ = lean_array_fset(v_es_842_, v_j_845_, v___x_852_);
switch(lean_obj_tag(v_v_851_))
{
case 0:
{
lean_object* v_key_860_; lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
v_key_860_ = lean_ctor_get(v_v_851_, 0);
v_val_861_ = lean_ctor_get(v_v_851_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_v_851_);
if (v_isSharedCheck_871_ == 0)
{
v___x_863_ = v_v_851_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_inc(v_key_860_);
lean_dec(v_v_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___x_865_; 
v___x_865_ = l_Lean_instBEqFVarId_beq(v_x_840_, v_key_860_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_del_object(v___x_863_);
v___x_866_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_860_, v_val_861_, v_x_840_, v_x_841_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___y_855_ = v___x_867_;
goto v___jp_854_;
}
else
{
lean_object* v___x_869_; 
lean_dec(v_val_861_);
lean_dec(v_key_860_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_x_841_);
lean_ctor_set(v___x_863_, 0, v_x_840_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_x_840_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_x_841_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v___y_855_ = v___x_869_;
goto v___jp_854_;
}
}
}
}
case 1:
{
lean_object* v_node_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_884_; 
v_node_872_ = lean_ctor_get(v_v_851_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_v_851_);
if (v_isSharedCheck_884_ == 0)
{
v___x_874_ = v_v_851_;
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_node_872_);
lean_dec(v_v_851_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_876_ = ((size_t)5ULL);
v___x_877_ = lean_usize_shift_right(v_x_838_, v___x_876_);
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_x_839_, v___x_878_);
v___x_880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_node_872_, v___x_877_, v___x_879_, v_x_840_, v_x_841_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_880_);
v___x_882_ = v___x_874_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
v___y_855_ = v___x_882_;
goto v___jp_854_;
}
}
}
default: 
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_x_840_);
lean_ctor_set(v___x_885_, 1, v_x_841_);
v___y_855_ = v___x_885_;
goto v___jp_854_;
}
}
v___jp_854_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_array_fset(v_xs_x27_853_, v_j_845_, v___y_855_);
lean_dec(v_j_845_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_856_);
v___x_858_ = v___x_849_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_object* v_ks_888_; lean_object* v_vs_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_907_; 
v_ks_888_ = lean_ctor_get(v_x_837_, 0);
v_vs_889_ = lean_ctor_get(v_x_837_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_907_ == 0)
{
v___x_891_ = v_x_837_;
v_isShared_892_ = v_isSharedCheck_907_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_vs_889_);
lean_inc(v_ks_888_);
lean_dec(v_x_837_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_907_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_ks_888_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_vs_889_);
v___x_894_ = v_reuseFailAlloc_906_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v_newNode_895_; size_t v___x_896_; uint8_t v___x_897_; 
v_newNode_895_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v___x_894_, v_x_840_, v_x_841_);
v___x_896_ = ((size_t)7ULL);
v___x_897_ = lean_usize_dec_le(v___x_896_, v_x_839_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_895_);
v___x_899_ = lean_unsigned_to_nat(4u);
v___x_900_ = lean_nat_dec_lt(v___x_898_, v___x_899_);
lean_dec(v___x_898_);
if (v___x_900_ == 0)
{
lean_object* v_ks_901_; lean_object* v_vs_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_ks_901_ = lean_ctor_get(v_newNode_895_, 0);
lean_inc_ref(v_ks_901_);
v_vs_902_ = lean_ctor_get(v_newNode_895_, 1);
lean_inc_ref(v_vs_902_);
lean_dec_ref(v_newNode_895_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0);
v___x_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_x_839_, v_ks_901_, v_vs_902_, v___x_903_, v___x_904_);
lean_dec_ref(v_vs_902_);
lean_dec_ref(v_ks_901_);
return v___x_905_;
}
else
{
return v_newNode_895_;
}
}
else
{
return v_newNode_895_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_837_ = stack[0].m_obj;
size_t v_x_838_ = stack[1].m_num;
size_t v_x_839_ = stack[2].m_num;
lean_object* v_x_840_ = stack[3].m_obj;
lean_object* v_x_841_ = stack[4].m_obj;
lean_object* v_res_908_;
v_res_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_837_, v_x_838_, v_x_839_, v_x_840_, v_x_841_);
stack->m_obj
 = v_res_908_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t v_depth_909_, lean_object* v_keys_910_, lean_object* v_vals_911_, lean_object* v_i_912_, lean_object* v_entries_913_){
_start:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_array_get_size(v_keys_910_);
v___x_915_ = lean_nat_dec_lt(v_i_912_, v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v_i_912_);
return v_entries_913_;
}
else
{
lean_object* v_k_916_; lean_object* v_v_917_; uint64_t v___x_918_; size_t v_h_919_; size_t v___x_920_; lean_object* v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v_h_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_k_916_ = lean_array_fget_borrowed(v_keys_910_, v_i_912_);
v_v_917_ = lean_array_fget_borrowed(v_vals_911_, v_i_912_);
v___x_918_ = l_Lean_instHashableFVarId_hash(v_k_916_);
v_h_919_ = lean_uint64_to_usize(v___x_918_);
v___x_920_ = ((size_t)5ULL);
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_sub(v_depth_909_, v___x_922_);
v___x_924_ = lean_usize_mul(v___x_920_, v___x_923_);
v_h_925_ = lean_usize_shift_right(v_h_919_, v___x_924_);
v___x_926_ = lean_nat_add(v_i_912_, v___x_921_);
lean_dec(v_i_912_);
lean_inc(v_v_917_);
lean_inc(v_k_916_);
v___x_927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_entries_913_, v_h_925_, v_depth_909_, v_k_916_, v_v_917_);
v_i_912_ = v___x_926_;
v_entries_913_ = v___x_927_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_909_ = stack[0].m_num;
lean_object* v_keys_910_ = stack[1].m_obj;
lean_object* v_vals_911_ = stack[2].m_obj;
lean_object* v_i_912_ = stack[3].m_obj;
lean_object* v_entries_913_ = stack[4].m_obj;
lean_object* v_res_929_;
v_res_929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_909_, v_keys_910_, v_vals_911_, v_i_912_, v_entries_913_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_depth_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_i_933_, lean_object* v_entries_934_){
_start:
{
size_t v_depth_boxed_935_; lean_object* v_res_936_; 
v_depth_boxed_935_ = lean_unbox_usize(v_depth_930_);
lean_dec(v_depth_930_);
v_res_936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_boxed_935_, v_keys_931_, v_vals_932_, v_i_933_, v_entries_934_);
lean_dec_ref(v_vals_932_);
lean_dec_ref(v_keys_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
size_t v_x_26677__boxed_942_; size_t v_x_26678__boxed_943_; lean_object* v_res_944_; 
v_x_26677__boxed_942_ = lean_unbox_usize(v_x_938_);
lean_dec(v_x_938_);
v_x_26678__boxed_943_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_937_, v_x_26677__boxed_942_, v_x_26678__boxed_943_, v_x_940_, v_x_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint64_t v___x_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; 
v___x_948_ = l_Lean_instHashableFVarId_hash(v_x_946_);
v___x_949_ = lean_uint64_to_usize(v___x_948_);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_945_, v___x_949_, v___x_950_, v_x_946_, v_x_947_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object* v_a_952_, lean_object* v_b_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_dec(v_b_953_);
lean_dec_ref(v_a_952_);
return v_x_954_;
}
else
{
lean_object* v_key_955_; lean_object* v_value_956_; lean_object* v_tail_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_969_; 
v_key_955_ = lean_ctor_get(v_x_954_, 0);
v_value_956_ = lean_ctor_get(v_x_954_, 1);
v_tail_957_ = lean_ctor_get(v_x_954_, 2);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_954_);
if (v_isSharedCheck_969_ == 0)
{
v___x_959_ = v_x_954_;
v_isShared_960_ = v_isSharedCheck_969_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_tail_957_);
lean_inc(v_value_956_);
lean_inc(v_key_955_);
lean_dec(v_x_954_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_969_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
uint8_t v___x_961_; 
v___x_961_ = l_Lean_ExprStructEq_beq(v_key_955_, v_a_952_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_952_, v_b_953_, v_tail_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 2, v___x_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_key_955_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_value_956_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v___x_967_; 
lean_dec(v_value_956_);
lean_dec(v_key_955_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v_b_953_);
lean_ctor_set(v___x_959_, 0, v_a_952_);
v___x_967_ = v___x_959_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_952_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_b_953_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_tail_957_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object* v_a_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_x_971_) == 0)
{
uint8_t v___x_972_; 
v___x_972_ = 0;
return v___x_972_;
}
else
{
lean_object* v_key_973_; lean_object* v_tail_974_; uint8_t v___x_975_; 
v_key_973_ = lean_ctor_get(v_x_971_, 0);
v_tail_974_ = lean_ctor_get(v_x_971_, 2);
v___x_975_ = l_Lean_ExprStructEq_beq(v_key_973_, v_a_970_);
if (v___x_975_ == 0)
{
v_x_971_ = v_tail_974_;
goto _start;
}
else
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_970_ = stack[0].m_obj;
lean_object* v_x_971_ = stack[1].m_obj;
uint8_t v_res_977_;
v_res_977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_970_, v_x_971_);
stack->m_num = v_res_977_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object* v_a_978_, lean_object* v_x_979_){
_start:
{
uint8_t v_res_980_; lean_object* v_r_981_; 
v_res_980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_978_, v_x_979_);
lean_dec(v_x_979_);
lean_dec_ref(v_a_978_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
return v_x_982_;
}
else
{
lean_object* v_key_984_; lean_object* v_value_985_; lean_object* v_tail_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1009_; 
v_key_984_ = lean_ctor_get(v_x_983_, 0);
v_value_985_ = lean_ctor_get(v_x_983_, 1);
v_tail_986_ = lean_ctor_get(v_x_983_, 2);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_983_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_988_ = v_x_983_;
v_isShared_989_ = v_isSharedCheck_1009_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_tail_986_);
lean_inc(v_value_985_);
lean_inc(v_key_984_);
lean_dec(v_x_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1009_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; uint64_t v___x_991_; uint64_t v___x_992_; uint64_t v___x_993_; uint64_t v_fold_994_; uint64_t v___x_995_; uint64_t v___x_996_; uint64_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_990_ = lean_array_get_size(v_x_982_);
v___x_991_ = l_Lean_ExprStructEq_hash(v_key_984_);
v___x_992_ = 32ULL;
v___x_993_ = lean_uint64_shift_right(v___x_991_, v___x_992_);
v_fold_994_ = lean_uint64_xor(v___x_991_, v___x_993_);
v___x_995_ = 16ULL;
v___x_996_ = lean_uint64_shift_right(v_fold_994_, v___x_995_);
v___x_997_ = lean_uint64_xor(v_fold_994_, v___x_996_);
v___x_998_ = lean_uint64_to_usize(v___x_997_);
v___x_999_ = lean_usize_of_nat(v___x_990_);
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_sub(v___x_999_, v___x_1000_);
v___x_1002_ = lean_usize_land(v___x_998_, v___x_1001_);
v___x_1003_ = lean_array_uget_borrowed(v_x_982_, v___x_1002_);
lean_inc(v___x_1003_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 2, v___x_1003_);
v___x_1005_ = v___x_988_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_key_984_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_value_985_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_array_uset(v_x_982_, v___x_1002_, v___x_1005_);
v_x_982_ = v___x_1006_;
v_x_983_ = v_tail_986_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object* v_i_1010_, lean_object* v_source_1011_, lean_object* v_target_1012_){
_start:
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = lean_array_get_size(v_source_1011_);
v___x_1014_ = lean_nat_dec_lt(v_i_1010_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec_ref(v_source_1011_);
lean_dec(v_i_1010_);
return v_target_1012_;
}
else
{
lean_object* v_es_1015_; lean_object* v___x_1016_; lean_object* v_source_1017_; lean_object* v_target_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_es_1015_ = lean_array_fget(v_source_1011_, v_i_1010_);
v___x_1016_ = lean_box(0);
v_source_1017_ = lean_array_fset(v_source_1011_, v_i_1010_, v___x_1016_);
v_target_1018_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_target_1012_, v_es_1015_);
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_i_1010_, v___x_1019_);
lean_dec(v_i_1010_);
v_i_1010_ = v___x_1020_;
v_source_1011_ = v_source_1017_;
v_target_1012_ = v_target_1018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object* v_data_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_nbuckets_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1023_ = lean_array_get_size(v_data_1022_);
v___x_1024_ = lean_unsigned_to_nat(2u);
v_nbuckets_1025_ = lean_nat_mul(v___x_1023_, v___x_1024_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_mk_array(v_nbuckets_1025_, v___x_1027_);
v___x_1029_ = lean_array_propagate_mark(v_data_1022_, v___x_1028_);
v___x_1030_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v___x_1026_, v_data_1022_, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_m_1031_, lean_object* v_a_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v_size_1034_; lean_object* v_buckets_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1078_; 
v_size_1034_ = lean_ctor_get(v_m_1031_, 0);
v_buckets_1035_ = lean_ctor_get(v_m_1031_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_m_1031_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1037_ = v_m_1031_;
v_isShared_1038_ = v_isSharedCheck_1078_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_buckets_1035_);
lean_inc(v_size_1034_);
lean_dec(v_m_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1078_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; uint64_t v_fold_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v_bkt_1052_; uint8_t v___x_1053_; 
v___x_1039_ = lean_array_get_size(v_buckets_1035_);
v___x_1040_ = l_Lean_ExprStructEq_hash(v_a_1032_);
v___x_1041_ = 32ULL;
v___x_1042_ = lean_uint64_shift_right(v___x_1040_, v___x_1041_);
v_fold_1043_ = lean_uint64_xor(v___x_1040_, v___x_1042_);
v___x_1044_ = 16ULL;
v___x_1045_ = lean_uint64_shift_right(v_fold_1043_, v___x_1044_);
v___x_1046_ = lean_uint64_xor(v_fold_1043_, v___x_1045_);
v___x_1047_ = lean_uint64_to_usize(v___x_1046_);
v___x_1048_ = lean_usize_of_nat(v___x_1039_);
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_sub(v___x_1048_, v___x_1049_);
v___x_1051_ = lean_usize_land(v___x_1047_, v___x_1050_);
v_bkt_1052_ = lean_array_uget_borrowed(v_buckets_1035_, v___x_1051_);
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1032_, v_bkt_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v_size_x27_1055_; lean_object* v___x_1056_; lean_object* v_buckets_x27_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1054_ = lean_unsigned_to_nat(1u);
v_size_x27_1055_ = lean_nat_add(v_size_1034_, v___x_1054_);
lean_dec(v_size_1034_);
lean_inc(v_bkt_1052_);
v___x_1056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1032_);
lean_ctor_set(v___x_1056_, 1, v_b_1033_);
lean_ctor_set(v___x_1056_, 2, v_bkt_1052_);
v_buckets_x27_1057_ = lean_array_uset(v_buckets_1035_, v___x_1051_, v___x_1056_);
v___x_1058_ = lean_unsigned_to_nat(4u);
v___x_1059_ = lean_nat_mul(v_size_x27_1055_, v___x_1058_);
v___x_1060_ = lean_unsigned_to_nat(3u);
v___x_1061_ = lean_nat_div(v___x_1059_, v___x_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_array_get_size(v_buckets_x27_1057_);
v___x_1063_ = lean_nat_dec_le(v___x_1061_, v___x_1062_);
lean_dec(v___x_1061_);
if (v___x_1063_ == 0)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; 
v_val_1064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_buckets_x27_1057_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_val_1064_);
lean_ctor_set(v___x_1037_, 0, v_size_x27_1055_);
v___x_1066_ = v___x_1037_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_size_x27_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_val_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v___x_1069_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_buckets_x27_1057_);
lean_ctor_set(v___x_1037_, 0, v_size_x27_1055_);
v___x_1069_ = v___x_1037_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_size_x27_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_buckets_x27_1057_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v_buckets_x27_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
lean_inc(v_bkt_1052_);
v___x_1071_ = lean_box(0);
v_buckets_x27_1072_ = lean_array_uset(v_buckets_1035_, v___x_1051_, v___x_1071_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1032_, v_b_1033_, v_bkt_1052_);
v___x_1074_ = lean_array_uset(v_buckets_x27_1072_, v___x_1051_, v___x_1073_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1074_);
v___x_1076_ = v___x_1037_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_size_1034_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object* v_a_1079_, lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
else
{
lean_object* v_key_1082_; lean_object* v_value_1083_; lean_object* v_tail_1084_; uint8_t v___x_1085_; 
v_key_1082_ = lean_ctor_get(v_x_1080_, 0);
v_value_1083_ = lean_ctor_get(v_x_1080_, 1);
v_tail_1084_ = lean_ctor_get(v_x_1080_, 2);
v___x_1085_ = l_Lean_ExprStructEq_beq(v_key_1082_, v_a_1079_);
if (v___x_1085_ == 0)
{
v_x_1080_ = v_tail_1084_;
goto _start;
}
else
{
lean_object* v___x_1087_; 
lean_inc(v_value_1083_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_value_1083_);
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object* v_a_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1088_, v_x_1089_);
lean_dec(v_x_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_m_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_buckets_1093_; lean_object* v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; uint64_t v_fold_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_buckets_1093_ = lean_ctor_get(v_m_1091_, 1);
v___x_1094_ = lean_array_get_size(v_buckets_1093_);
v___x_1095_ = l_Lean_ExprStructEq_hash(v_a_1092_);
v___x_1096_ = 32ULL;
v___x_1097_ = lean_uint64_shift_right(v___x_1095_, v___x_1096_);
v_fold_1098_ = lean_uint64_xor(v___x_1095_, v___x_1097_);
v___x_1099_ = 16ULL;
v___x_1100_ = lean_uint64_shift_right(v_fold_1098_, v___x_1099_);
v___x_1101_ = lean_uint64_xor(v_fold_1098_, v___x_1100_);
v___x_1102_ = lean_uint64_to_usize(v___x_1101_);
v___x_1103_ = lean_usize_of_nat(v___x_1094_);
v___x_1104_ = ((size_t)1ULL);
v___x_1105_ = lean_usize_sub(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_usize_land(v___x_1102_, v___x_1105_);
v___x_1107_ = lean_array_uget_borrowed(v_buckets_1093_, v___x_1106_);
v___x_1108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1092_, v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object* v_m_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1109_, v_a_1110_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_m_1109_);
return v_res_1111_;
}
}
lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(lean_object* v_proof_1112_, uint8_t v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; 
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1115_);
v___x_1120_ = lean_infer_type(v_proof_1112_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_1112_ = stack[0].m_obj;
uint8_t v___y_1113_ = stack[1].m_num;
lean_object* v___y_1114_ = stack[2].m_obj;
lean_object* v___y_1115_ = stack[3].m_obj;
lean_object* v___y_1116_ = stack[4].m_obj;
lean_object* v___y_1117_ = stack[5].m_obj;
lean_object* v___y_1118_ = stack[6].m_obj;
lean_object* v_res_1121_;
v_res_1121_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(v_proof_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
stack->m_obj
 = v_res_1121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed(lean_object* v_proof_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v___y_27314__boxed_1130_; lean_object* v_res_1131_; 
v___y_27314__boxed_1130_ = lean_unbox(v___y_1123_);
v_res_1131_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0(v_proof_1122_, v___y_27314__boxed_1130_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
return v_res_1131_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(lean_object* v_x_1132_, uint8_t v_isExporting_1133_, uint8_t v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v_env_1142_; lean_object* v___x_1143_; uint8_t v_isModule_1144_; 
v___x_1141_ = lean_st_ref_get(v___y_1139_);
v_env_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_env_1142_);
lean_dec(v___x_1141_);
v___x_1143_ = l_Lean_Environment_header(v_env_1142_);
v_isModule_1144_ = lean_ctor_get_uint8(v___x_1143_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1143_);
if (v_isModule_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_env_1142_);
v___x_1145_ = lean_box(v___y_1134_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
v___x_1146_ = lean_apply_7(v_x_1132_, v___x_1145_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1146_;
}
else
{
uint8_t v_isExporting_1147_; 
v_isExporting_1147_ = lean_ctor_get_uint8(v_env_1142_, sizeof(void*)*13);
lean_dec_ref(v_env_1142_);
if (v_isExporting_1133_ == 0)
{
if (v_isExporting_1147_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_box(v___y_1134_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
v___x_1216_ = lean_apply_7(v_x_1132_, v___x_1215_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1216_;
}
else
{
goto v___jp_1148_;
}
}
else
{
if (v_isExporting_1147_ == 0)
{
goto v___jp_1148_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_box(v___y_1134_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
v___x_1218_ = lean_apply_7(v_x_1132_, v___x_1217_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1218_;
}
}
v___jp_1148_:
{
lean_object* v___x_1149_; lean_object* v_env_1150_; lean_object* v_nextMacroScope_1151_; lean_object* v_ngen_1152_; lean_object* v_auxDeclNGen_1153_; lean_object* v_traceState_1154_; lean_object* v_recordedDeps_1155_; lean_object* v_messages_1156_; lean_object* v_infoState_1157_; lean_object* v_snapshotTasks_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1213_; 
v___x_1149_ = lean_st_ref_take(v___y_1139_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
v_nextMacroScope_1151_ = lean_ctor_get(v___x_1149_, 1);
v_ngen_1152_ = lean_ctor_get(v___x_1149_, 2);
v_auxDeclNGen_1153_ = lean_ctor_get(v___x_1149_, 3);
v_traceState_1154_ = lean_ctor_get(v___x_1149_, 4);
v_recordedDeps_1155_ = lean_ctor_get(v___x_1149_, 6);
v_messages_1156_ = lean_ctor_get(v___x_1149_, 7);
v_infoState_1157_ = lean_ctor_get(v___x_1149_, 8);
v_snapshotTasks_1158_ = lean_ctor_get(v___x_1149_, 9);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1149_, 5);
lean_dec(v_unused_1214_);
v___x_1160_ = v___x_1149_;
v_isShared_1161_ = v_isSharedCheck_1213_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snapshotTasks_1158_);
lean_inc(v_infoState_1157_);
lean_inc(v_messages_1156_);
lean_inc(v_recordedDeps_1155_);
lean_inc(v_traceState_1154_);
lean_inc(v_auxDeclNGen_1153_);
lean_inc(v_ngen_1152_);
lean_inc(v_nextMacroScope_1151_);
lean_inc(v_env_1150_);
lean_dec(v___x_1149_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1213_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = l_Lean_Environment_setExporting(v_env_1150_, v_isExporting_1133_);
v___x_1163_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__2);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 5, v___x_1163_);
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_nextMacroScope_1151_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_ngen_1152_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_auxDeclNGen_1153_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_traceState_1154_);
lean_ctor_set(v_reuseFailAlloc_1212_, 5, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1212_, 6, v_recordedDeps_1155_);
lean_ctor_set(v_reuseFailAlloc_1212_, 7, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1212_, 8, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1212_, 9, v_snapshotTasks_1158_);
v___x_1165_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_mctx_1168_; lean_object* v_zetaDeltaFVarIds_1169_; lean_object* v_postponed_1170_; lean_object* v_diag_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1210_; 
v___x_1166_ = lean_st_ref_put(v___y_1139_, v___x_1165_);
v___x_1167_ = lean_st_ref_take(v___y_1137_);
v_mctx_1168_ = lean_ctor_get(v___x_1167_, 0);
v_zetaDeltaFVarIds_1169_ = lean_ctor_get(v___x_1167_, 2);
v_postponed_1170_ = lean_ctor_get(v___x_1167_, 3);
v_diag_1171_ = lean_ctor_get(v___x_1167_, 4);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v___x_1167_, 1);
lean_dec(v_unused_1211_);
v___x_1173_ = v___x_1167_;
v_isShared_1174_ = v_isSharedCheck_1210_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_diag_1171_);
lean_inc(v_postponed_1170_);
lean_inc(v_zetaDeltaFVarIds_1169_);
lean_inc(v_mctx_1168_);
lean_dec(v___x_1167_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1210_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___closed__3);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_mctx_1168_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_zetaDeltaFVarIds_1169_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_postponed_1170_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_diag_1171_);
v___x_1177_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_r_1180_; 
v___x_1178_ = lean_st_ref_put(v___y_1137_, v___x_1177_);
v___x_1179_ = lean_box(v___y_1134_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
v_r_1180_ = lean_apply_7(v_x_1132_, v___x_1179_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
if (lean_obj_tag(v_r_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1197_; 
v_a_1181_ = lean_ctor_get(v_r_1180_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_r_1180_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1183_ = v_r_1180_;
v_isShared_1184_ = v_isSharedCheck_1197_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v_r_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1197_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
lean_inc(v_a_1181_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 1);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v___x_1187_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_1139_, v_isExporting_1147_, v___x_1163_, v___y_1137_, v___x_1175_, v___x_1186_);
lean_dec_ref(v___x_1186_);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1187_, 0);
lean_dec(v_unused_1195_);
v___x_1189_ = v___x_1187_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v___x_1187_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_a_1181_);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1181_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1198_ = lean_ctor_get(v_r_1180_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v_r_1180_, 1);
v___x_1199_ = lean_box(0);
v___x_1200_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__3___redArg___lam__0(v___y_1139_, v_isExporting_1147_, v___x_1163_, v___y_1137_, v___x_1175_, v___x_1199_);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1208_);
v___x_1202_ = v___x_1200_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v___x_1200_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 1);
lean_ctor_set(v___x_1202_, 0, v_a_1198_);
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1198_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1132_ = stack[0].m_obj;
uint8_t v_isExporting_1133_ = stack[1].m_num;
uint8_t v___y_1134_ = stack[2].m_num;
lean_object* v___y_1135_ = stack[3].m_obj;
lean_object* v___y_1136_ = stack[4].m_obj;
lean_object* v___y_1137_ = stack[5].m_obj;
lean_object* v___y_1138_ = stack[6].m_obj;
lean_object* v___y_1139_ = stack[7].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1132_, v_isExporting_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg___boxed(lean_object* v_x_1220_, lean_object* v_isExporting_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
uint8_t v_isExporting_boxed_1229_; uint8_t v___y_27365__boxed_1230_; lean_object* v_res_1231_; 
v_isExporting_boxed_1229_ = lean_unbox(v_isExporting_1221_);
v___y_27365__boxed_1230_ = lean_unbox(v___y_1222_);
v_res_1231_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1220_, v_isExporting_boxed_1229_, v___y_27365__boxed_1230_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
return v_res_1231_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(lean_object* v_x_1232_, uint8_t v_when_1233_, uint8_t v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
if (v_when_1233_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(v___y_1234_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
v___x_1242_ = lean_apply_7(v_x_1232_, v___x_1241_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, lean_box(0));
return v___x_1242_;
}
else
{
uint8_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = 0;
v___x_1244_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1232_, v___x_1243_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1244_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1232_ = stack[0].m_obj;
uint8_t v_when_1233_ = stack[1].m_num;
uint8_t v___y_1234_ = stack[2].m_num;
lean_object* v___y_1235_ = stack[3].m_obj;
lean_object* v___y_1236_ = stack[4].m_obj;
lean_object* v___y_1237_ = stack[5].m_obj;
lean_object* v___y_1238_ = stack[6].m_obj;
lean_object* v___y_1239_ = stack[7].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1232_, v_when_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg___boxed(lean_object* v_x_1246_, lean_object* v_when_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
uint8_t v_when_boxed_1255_; uint8_t v___y_27589__boxed_1256_; lean_object* v_res_1257_; 
v_when_boxed_1255_ = lean_unbox(v_when_1247_);
v___y_27589__boxed_1256_ = lean_unbox(v___y_1248_);
v_res_1257_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1246_, v_when_boxed_1255_, v___y_27589__boxed_1256_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
return v_res_1257_;
}
}
lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_proof_1258_, uint8_t v_cache_1259_, lean_object* v_postprocessType_1260_, uint8_t v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___f_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; 
lean_inc_ref(v_proof_1258_);
v___f_1268_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1268_, 0, v_proof_1258_);
v___x_1269_ = 1;
v___x_1270_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v___f_1268_, v___x_1269_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l_Lean_Core_betaReduce(v_a_1271_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l_Lean_Meta_zetaReduce(v_a_1273_, v___x_1269_, v___x_1269_, v___x_1269_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_box(v___y_1261_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
v___x_1277_ = lean_apply_8(v_postprocessType_1260_, v_a_1275_, v___x_1276_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, lean_box(0));
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; uint8_t v___y_1280_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
if (v_cache_1259_ == 0)
{
v___y_1280_ = v_cache_1259_;
goto v___jp_1279_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = l_Lean_Expr_hasSorry(v_proof_1258_);
if (v___x_1283_ == 0)
{
v___y_1280_ = v_cache_1259_;
goto v___jp_1279_;
}
else
{
uint8_t v___x_1284_; 
v___x_1284_ = 0;
v___y_1280_ = v___x_1284_;
goto v___jp_1279_;
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Lean_Meta_mkAuxTheorem(v_a_1278_, v_proof_1258_, v___x_1269_, v___x_1281_, v___y_1280_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1282_;
}
}
else
{
lean_dec_ref(v_proof_1258_);
return v___x_1277_;
}
}
else
{
lean_dec_ref(v_postprocessType_1260_);
lean_dec_ref(v_proof_1258_);
return v___x_1274_;
}
}
else
{
lean_dec_ref(v_postprocessType_1260_);
lean_dec_ref(v_proof_1258_);
return v___x_1272_;
}
}
else
{
lean_dec_ref(v_postprocessType_1260_);
lean_dec_ref(v_proof_1258_);
return v___x_1270_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_1258_ = stack[0].m_obj;
uint8_t v_cache_1259_ = stack[1].m_num;
lean_object* v_postprocessType_1260_ = stack[2].m_obj;
uint8_t v___y_1261_ = stack[3].m_num;
lean_object* v___y_1262_ = stack[4].m_obj;
lean_object* v___y_1263_ = stack[5].m_obj;
lean_object* v___y_1264_ = stack[6].m_obj;
lean_object* v___y_1265_ = stack[7].m_obj;
lean_object* v___y_1266_ = stack[8].m_obj;
lean_object* v_res_1285_;
v_res_1285_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_proof_1258_, v_cache_1259_, v_postprocessType_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_proof_1286_, lean_object* v_cache_1287_, lean_object* v_postprocessType_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v_cache_boxed_1296_; uint8_t v___y_27636__boxed_1297_; lean_object* v_res_1298_; 
v_cache_boxed_1296_ = lean_unbox(v_cache_1287_);
v___y_27636__boxed_1297_ = lean_unbox(v___y_1289_);
v_res_1298_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_proof_1286_, v_cache_boxed_1296_, v_postprocessType_1288_, v___y_27636__boxed_1297_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
return v_res_1298_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_as_1299_, size_t v_sz_1300_, size_t v_i_1301_, lean_object* v_b_1302_, uint8_t v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_a_1311_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_lt(v_i_1301_, v_sz_1300_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_b_1302_);
return v___x_1325_;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v_localDecl_1329_; lean_object* v___x_1337_; 
v_a_1326_ = lean_array_uget_borrowed(v_as_1299_, v_i_1301_);
v___x_1327_ = l_Lean_Expr_fvarId_x21(v_a_1326_);
lean_inc(v___x_1327_);
v___x_1337_ = l_Lean_FVarId_getDecl___redArg(v___x_1327_, v___y_1305_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___x_1339_ = l_Lean_LocalDecl_type(v_a_1338_);
v___x_1340_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1339_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = l_Lean_LocalDecl_setType(v_a_1338_, v_a_1341_);
v___x_1343_ = l_Lean_LocalDecl_value_x3f(v___x_1342_, v___x_1324_);
if (lean_obj_tag(v___x_1343_) == 0)
{
v_localDecl_1329_ = v___x_1342_;
goto v___jp_1328_;
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1345_; 
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1344_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_LocalDecl_setValue(v___x_1342_, v_a_1346_);
v_localDecl_1329_ = v___x_1347_;
goto v___jp_1328_;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v___x_1342_);
lean_dec(v___x_1327_);
lean_dec_ref(v_b_1302_);
v_a_1348_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1345_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_a_1338_);
lean_dec(v___x_1327_);
lean_dec_ref(v_b_1302_);
v_a_1356_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1340_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1340_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v___x_1327_);
lean_dec_ref(v_b_1302_);
v_a_1364_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1337_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1337_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
v___jp_1328_:
{
lean_object* v_fvarIdToDecl_1330_; lean_object* v_decls_1331_; lean_object* v_auxDeclToFullName_1332_; lean_object* v___x_1333_; 
v_fvarIdToDecl_1330_ = lean_ctor_get(v_b_1302_, 0);
v_decls_1331_ = lean_ctor_get(v_b_1302_, 1);
v_auxDeclToFullName_1332_ = lean_ctor_get(v_b_1302_, 2);
lean_inc_ref(v_b_1302_);
v___x_1333_ = lean_local_ctx_find(v_b_1302_, v___x_1327_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref(v_localDecl_1329_);
v_a_1311_ = v_b_1302_;
goto v___jp_1310_;
}
else
{
lean_object* v_index_1334_; lean_object* v_fvarId_1335_; lean_object* v___x_1336_; 
lean_inc(v_auxDeclToFullName_1332_);
lean_inc_ref(v_decls_1331_);
lean_inc_ref(v_fvarIdToDecl_1330_);
lean_dec_ref_known(v___x_1333_, 1);
lean_dec_ref(v_b_1302_);
v_index_1334_ = lean_ctor_get(v_localDecl_1329_, 0);
lean_inc(v_index_1334_);
v_fvarId_1335_ = lean_ctor_get(v_localDecl_1329_, 1);
lean_inc_ref(v_localDecl_1329_);
lean_inc(v_fvarId_1335_);
v___x_1336_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_fvarIdToDecl_1330_, v_fvarId_1335_, v_localDecl_1329_);
v___y_1316_ = v_decls_1331_;
v___y_1317_ = v___x_1336_;
v___y_1318_ = v_localDecl_1329_;
v___y_1319_ = v_auxDeclToFullName_1332_;
v___y_1320_ = v_index_1334_;
goto v___jp_1315_;
}
}
}
v___jp_1310_:
{
size_t v___x_1312_; size_t v___x_1313_; 
v___x_1312_ = ((size_t)1ULL);
v___x_1313_ = lean_usize_add(v_i_1301_, v___x_1312_);
v_i_1301_ = v___x_1313_;
v_b_1302_ = v_a_1311_;
goto _start;
}
v___jp_1315_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___y_1318_);
v___x_1322_ = l_Lean_PersistentArray_set___redArg(v___y_1316_, v___y_1320_, v___x_1321_);
lean_dec(v___y_1320_);
v___x_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1323_, 0, v___y_1317_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
lean_ctor_set(v___x_1323_, 2, v___y_1319_);
v_a_1311_ = v___x_1323_;
goto v___jp_1310_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1299_ = stack[0].m_obj;
size_t v_sz_1300_ = stack[1].m_num;
size_t v_i_1301_ = stack[2].m_num;
lean_object* v_b_1302_ = stack[3].m_obj;
uint8_t v___y_1303_ = stack[4].m_num;
lean_object* v___y_1304_ = stack[5].m_obj;
lean_object* v___y_1305_ = stack[6].m_obj;
lean_object* v___y_1306_ = stack[7].m_obj;
lean_object* v___y_1307_ = stack[8].m_obj;
lean_object* v___y_1308_ = stack[9].m_obj;
lean_object* v_res_1372_;
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_as_1299_, v_sz_1300_, v_i_1301_, v_b_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
stack->m_obj
 = v_res_1372_;
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1373_, lean_object* v_k_1374_, uint8_t v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_lctx_1382_; lean_object* v_localInstances_1383_; size_t v_sz_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v_lctx_1382_ = lean_ctor_get(v___y_1377_, 2);
v_localInstances_1383_ = lean_ctor_get(v___y_1377_, 3);
v_sz_1384_ = lean_array_size(v_xs_1373_);
v___x_1385_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1382_);
v___x_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_xs_1373_, v_sz_1384_, v___x_1385_, v_lctx_1382_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
lean_inc_ref(v_localInstances_1383_);
v___x_1388_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_a_1387_, v_localInstances_1383_, v_k_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1388_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_k_1374_);
v_a_1389_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1386_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1386_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_visit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1373_ = stack[0].m_obj;
lean_object* v_k_1374_ = stack[1].m_obj;
uint8_t v___y_1375_ = stack[2].m_num;
lean_object* v___y_1376_ = stack[3].m_obj;
lean_object* v___y_1377_ = stack[4].m_obj;
lean_object* v___y_1378_ = stack[5].m_obj;
lean_object* v___y_1379_ = stack[6].m_obj;
lean_object* v___y_1380_ = stack[7].m_obj;
lean_object* v_res_1397_;
v_res_1397_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1373_, v_k_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
stack->m_obj
 = v_res_1397_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1398_, lean_object* v_k_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v___y_27778__boxed_1407_; lean_object* v_res_1408_; 
v___y_27778__boxed_1407_ = lean_unbox(v___y_1400_);
v_res_1408_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1398_, v_k_1399_, v___y_27778__boxed_1407_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v_xs_1398_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
uint8_t v_a_boxed_1418_; lean_object* v_res_1419_; 
v_a_boxed_1418_ = lean_unbox(v_a_1411_);
v_res_1419_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1410_, v_a_boxed_1418_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1420_, lean_object* v___f_1421_, lean_object* v_xs_1422_, lean_object* v_b_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v___y_27728__boxed_1431_; uint8_t v___y_27730__boxed_1432_; lean_object* v_res_1433_; 
v___y_27728__boxed_1431_ = lean_unbox(v___y_1420_);
v___y_27730__boxed_1432_ = lean_unbox(v___y_1424_);
v_res_1433_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_27728__boxed_1431_, v___f_1421_, v_xs_1422_, v_b_1423_, v___y_27730__boxed_1432_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
return v_res_1433_;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1434_, lean_object* v_xs_1435_, uint8_t v___y_1436_, uint8_t v___x_1437_, uint8_t v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1434_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = 1;
v___x_1448_ = l_Lean_Meta_mkForallFVars(v_xs_1435_, v_a_1446_, v___y_1436_, v___x_1437_, v___x_1437_, v___x_1447_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1448_;
}
else
{
return v___x_1445_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_visit___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1434_ = stack[0].m_obj;
lean_object* v_xs_1435_ = stack[1].m_obj;
uint8_t v___y_1436_ = stack[2].m_num;
uint8_t v___x_1437_ = stack[3].m_num;
uint8_t v___y_1438_ = stack[4].m_num;
lean_object* v___y_1439_ = stack[5].m_obj;
lean_object* v___y_1440_ = stack[6].m_obj;
lean_object* v___y_1441_ = stack[7].m_obj;
lean_object* v___y_1442_ = stack[8].m_obj;
lean_object* v___y_1443_ = stack[9].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1434_, v_xs_1435_, v___y_1436_, v___x_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1450_, lean_object* v_xs_1451_, lean_object* v___y_1452_, lean_object* v___x_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___y_27764__boxed_1461_; uint8_t v___x_27765__boxed_1462_; uint8_t v___y_27766__boxed_1463_; lean_object* v_res_1464_; 
v___y_27764__boxed_1461_ = lean_unbox(v___y_1452_);
v___x_27765__boxed_1462_ = lean_unbox(v___x_1453_);
v___y_27766__boxed_1463_ = lean_unbox(v___y_1454_);
v_res_1464_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1450_, v_xs_1451_, v___y_27764__boxed_1461_, v___x_27765__boxed_1462_, v___y_27766__boxed_1463_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v_xs_1451_);
return v_res_1464_;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1465_, uint8_t v___x_1466_, lean_object* v___f_1467_, lean_object* v_xs_1468_, lean_object* v_b_1469_, uint8_t v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1477_ = lean_box(v___y_1465_);
v___x_1478_ = lean_box(v___x_1466_);
lean_inc_ref(v_xs_1468_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1479_, 0, v_b_1469_);
lean_closure_set(v___f_1479_, 1, v_xs_1468_);
lean_closure_set(v___f_1479_, 2, v___x_1477_);
lean_closure_set(v___f_1479_, 3, v___x_1478_);
v___x_1480_ = lean_box(v___y_1470_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
v___x_1481_ = lean_apply_9(v___f_1467_, v_xs_1468_, v___f_1479_, v___x_1480_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, lean_box(0));
return v___x_1481_;
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_visit___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1465_ = stack[0].m_num;
uint8_t v___x_1466_ = stack[1].m_num;
lean_object* v___f_1467_ = stack[2].m_obj;
lean_object* v_xs_1468_ = stack[3].m_obj;
lean_object* v_b_1469_ = stack[4].m_obj;
uint8_t v___y_1470_ = stack[5].m_num;
lean_object* v___y_1471_ = stack[6].m_obj;
lean_object* v___y_1472_ = stack[7].m_obj;
lean_object* v___y_1473_ = stack[8].m_obj;
lean_object* v___y_1474_ = stack[9].m_obj;
lean_object* v___y_1475_ = stack[10].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_1465_, v___x_1466_, v___f_1467_, v_xs_1468_, v_b_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1483_, lean_object* v___x_1484_, lean_object* v___f_1485_, lean_object* v_xs_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___y_27739__boxed_1495_; uint8_t v___x_27740__boxed_1496_; uint8_t v___y_27742__boxed_1497_; lean_object* v_res_1498_; 
v___y_27739__boxed_1495_ = lean_unbox(v___y_1483_);
v___x_27740__boxed_1496_ = lean_unbox(v___x_1484_);
v___y_27742__boxed_1497_ = lean_unbox(v___y_1488_);
v_res_1498_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_27739__boxed_1495_, v___x_27740__boxed_1496_, v___f_1485_, v_xs_1486_, v_b_1487_, v___y_27742__boxed_1497_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1498_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1499_, size_t v_i_1500_, lean_object* v_bs_1501_, uint8_t v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_usize_dec_lt(v_i_1500_, v_sz_1499_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_bs_1501_);
return v___x_1510_;
}
else
{
lean_object* v_v_1511_; lean_object* v___x_1512_; lean_object* v_bs_x27_1513_; lean_object* v___x_1514_; 
v_v_1511_ = lean_array_uget(v_bs_1501_, v_i_1500_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v_bs_x27_1513_ = lean_array_uset(v_bs_1501_, v_i_1500_, v___x_1512_);
v___x_1514_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1511_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1500_, v___x_1516_);
v___x_1518_ = lean_array_uset(v_bs_x27_1513_, v_i_1500_, v_a_1515_);
v_i_1500_ = v___x_1517_;
v_bs_1501_ = v___x_1518_;
goto _start;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v_bs_x27_1513_);
v_a_1520_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1514_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1514_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1499_ = stack[0].m_num;
size_t v_i_1500_ = stack[1].m_num;
lean_object* v_bs_1501_ = stack[2].m_obj;
uint8_t v___y_1502_ = stack[3].m_num;
lean_object* v___y_1503_ = stack[4].m_obj;
lean_object* v___y_1504_ = stack[5].m_obj;
lean_object* v___y_1505_ = stack[6].m_obj;
lean_object* v___y_1506_ = stack[7].m_obj;
lean_object* v___y_1507_ = stack[8].m_obj;
lean_object* v_res_1528_;
v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1499_, v_i_1500_, v_bs_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
stack->m_obj
 = v_res_1528_;
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, uint8_t v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 5)
{
lean_object* v_fn_1539_; lean_object* v_arg_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_fn_1539_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_ref(v_fn_1539_);
v_arg_1540_ = lean_ctor_get(v_x_1529_, 1);
lean_inc_ref(v_arg_1540_);
lean_dec_ref_known(v_x_1529_, 2);
v___x_1541_ = lean_array_set(v_x_1530_, v_x_1531_, v_arg_1540_);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_sub(v_x_1531_, v___x_1542_);
lean_dec(v_x_1531_);
v_x_1529_ = v_fn_1539_;
v_x_1530_ = v___x_1541_;
v_x_1531_ = v___x_1543_;
goto _start;
}
else
{
lean_object* v___x_1545_; 
lean_dec(v_x_1531_);
v___x_1545_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1529_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; size_t v_sz_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v_sz_1547_ = lean_array_size(v_x_1530_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1547_, v___x_1548_, v_x_1530_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1558_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = l_Lean_mkAppN(v_a_1546_, v_a_1550_);
lean_dec(v_a_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1554_);
v___x_1556_ = v___x_1552_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1546_);
v_a_1559_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1549_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1549_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_dec_ref(v_x_1530_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1529_ = stack[0].m_obj;
lean_object* v_x_1530_ = stack[1].m_obj;
lean_object* v_x_1531_ = stack[2].m_obj;
uint8_t v___y_1532_ = stack[3].m_num;
lean_object* v___y_1533_ = stack[4].m_obj;
lean_object* v___y_1534_ = stack[5].m_obj;
lean_object* v___y_1535_ = stack[6].m_obj;
lean_object* v___y_1536_ = stack[7].m_obj;
lean_object* v___y_1537_ = stack[8].m_obj;
lean_object* v_res_1567_;
v_res_1567_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1529_, v_x_1530_, v_x_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
stack->m_obj
 = v_res_1567_;
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1568_, uint8_t v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_a_1577_; lean_object* v___y_1583_; lean_object* v___f_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___f_1585_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1586_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1587_ = l_Lean_Core_checkSystem(v___x_1586_, v_a_1573_, v_a_1574_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1652_; 
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v___x_1587_, 0);
lean_dec(v_unused_1653_);
v___x_1589_ = v___x_1587_;
v_isShared_1590_ = v_isSharedCheck_1652_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v___x_1587_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1652_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
uint8_t v___x_1591_; 
v___x_1591_ = l_Lean_Expr_isAtomic(v_e_1568_);
if (v___x_1591_ == 0)
{
uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = 1;
v___x_1593_ = lean_st_ref_get(v_a_1570_);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v___x_1593_, v_e_1568_);
lean_dec(v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
lean_del_object(v___x_1589_);
lean_inc_ref(v_e_1568_);
v___x_1595_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1568_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___y_1601_; uint8_t v___x_1635_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1635_ = lean_unbox(v_a_1596_);
lean_dec(v_a_1596_);
if (v___x_1635_ == 0)
{
v___y_1601_ = v___x_1591_;
goto v___jp_1600_;
}
else
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Lean_Expr_hasSorry(v_e_1568_);
if (v___x_1636_ == 0)
{
lean_dec_ref(v___f_1585_);
goto v___jp_1597_;
}
else
{
v___y_1601_ = v___x_1591_;
goto v___jp_1600_;
}
}
v___jp_1597_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1568_);
v___x_1599_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_e_1568_, v_a_1569_, v___x_1598_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
v___y_1583_ = v___x_1599_;
goto v___jp_1582_;
}
v___jp_1600_:
{
if (v___y_1601_ == 0)
{
switch(lean_obj_tag(v_e_1568_))
{
case 6:
{
lean_object* v___x_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_box(v___y_1601_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1603_, 0, v___x_1602_);
lean_closure_set(v___f_1603_, 1, v___f_1585_);
lean_inc_ref(v_e_1568_);
v___x_1604_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1568_, v___f_1603_, v___y_1601_, v___x_1592_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
v___y_1583_ = v___x_1604_;
goto v___jp_1582_;
}
case 8:
{
lean_object* v___x_1605_; lean_object* v___f_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_box(v___y_1601_);
v___f_1606_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1606_, 0, v___x_1605_);
lean_closure_set(v___f_1606_, 1, v___f_1585_);
lean_inc_ref(v_e_1568_);
v___x_1607_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1568_, v___f_1606_, v___y_1601_, v___x_1592_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
v___y_1583_ = v___x_1607_;
goto v___jp_1582_;
}
case 7:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; 
v___x_1608_ = lean_box(v___y_1601_);
v___x_1609_ = lean_box(v___x_1592_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1610_, 0, v___x_1608_);
lean_closure_set(v___f_1610_, 1, v___x_1609_);
lean_closure_set(v___f_1610_, 2, v___f_1585_);
lean_inc_ref(v_e_1568_);
v___x_1611_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___redArg(v_e_1568_, v___f_1610_, v___y_1601_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
v___y_1583_ = v___x_1611_;
goto v___jp_1582_;
}
case 10:
{
lean_object* v_data_1612_; lean_object* v_expr_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v___f_1585_);
v_data_1612_ = lean_ctor_get(v_e_1568_, 0);
v_expr_1613_ = lean_ctor_get(v_e_1568_, 1);
lean_inc_ref(v_expr_1613_);
v___x_1614_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1613_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; size_t v___x_1616_; size_t v___x_1617_; uint8_t v___x_1618_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = lean_ptr_addr(v_expr_1613_);
v___x_1617_ = lean_ptr_addr(v_a_1615_);
v___x_1618_ = lean_usize_dec_eq(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_inc(v_data_1612_);
v___x_1619_ = l_Lean_Expr_mdata___override(v_data_1612_, v_a_1615_);
v_a_1577_ = v___x_1619_;
goto v___jp_1576_;
}
else
{
lean_dec(v_a_1615_);
lean_inc_ref(v_e_1568_);
v_a_1577_ = v_e_1568_;
goto v___jp_1576_;
}
}
else
{
v___y_1583_ = v___x_1614_;
goto v___jp_1582_;
}
}
case 11:
{
lean_object* v_typeName_1620_; lean_object* v_idx_1621_; lean_object* v_struct_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v___f_1585_);
v_typeName_1620_ = lean_ctor_get(v_e_1568_, 0);
v_idx_1621_ = lean_ctor_get(v_e_1568_, 1);
v_struct_1622_ = lean_ctor_get(v_e_1568_, 2);
lean_inc_ref(v_struct_1622_);
v___x_1623_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1622_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; size_t v___x_1625_; size_t v___x_1626_; uint8_t v___x_1627_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = lean_ptr_addr(v_struct_1622_);
v___x_1626_ = lean_ptr_addr(v_a_1624_);
v___x_1627_ = lean_usize_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_inc(v_idx_1621_);
lean_inc(v_typeName_1620_);
v___x_1628_ = l_Lean_Expr_proj___override(v_typeName_1620_, v_idx_1621_, v_a_1624_);
v_a_1577_ = v___x_1628_;
goto v___jp_1576_;
}
else
{
lean_dec(v_a_1624_);
lean_inc_ref(v_e_1568_);
v_a_1577_ = v_e_1568_;
goto v___jp_1576_;
}
}
else
{
v___y_1583_ = v___x_1623_;
goto v___jp_1582_;
}
}
case 5:
{
lean_object* v_dummy_1629_; lean_object* v_nargs_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v___f_1585_);
v_dummy_1629_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1630_ = l_Lean_Expr_getAppNumArgs(v_e_1568_);
lean_inc(v_nargs_1630_);
v___x_1631_ = lean_mk_array(v_nargs_1630_, v_dummy_1629_);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_nat_sub(v_nargs_1630_, v___x_1632_);
lean_dec(v_nargs_1630_);
lean_inc_ref(v_e_1568_);
v___x_1634_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1568_, v___x_1631_, v___x_1633_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
v___y_1583_ = v___x_1634_;
goto v___jp_1582_;
}
default: 
{
lean_dec_ref(v___f_1585_);
lean_inc_ref(v_e_1568_);
v_a_1577_ = v_e_1568_;
goto v___jp_1576_;
}
}
}
else
{
lean_dec_ref(v___f_1585_);
goto v___jp_1597_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v___f_1585_);
lean_dec_ref(v_e_1568_);
v_a_1637_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1595_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1595_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; 
lean_dec_ref(v___f_1585_);
lean_dec_ref(v_e_1568_);
v_val_1645_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v___x_1594_, 1);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_val_1645_);
v___x_1647_ = v___x_1589_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_val_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v___x_1650_; 
lean_dec_ref(v___f_1585_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_e_1568_);
v___x_1650_ = v___x_1589_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_e_1568_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v___f_1585_);
lean_dec_ref(v_e_1568_);
v_a_1654_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1587_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1587_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
v___jp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = lean_st_ref_take(v_a_1570_);
lean_inc_ref(v_a_1577_);
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v___x_1578_, v_e_1568_, v_a_1577_);
v___x_1580_ = lean_st_ref_put(v_a_1570_, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_a_1577_);
return v___x_1581_;
}
v___jp_1582_:
{
if (lean_obj_tag(v___y_1583_) == 0)
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v___y_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___y_1583_, 1);
v_a_1577_ = v_a_1584_;
goto v___jp_1576_;
}
else
{
lean_dec_ref(v_e_1568_);
return v___y_1583_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1568_ = stack[0].m_obj;
uint8_t v_a_1569_ = stack[1].m_num;
lean_object* v_a_1570_ = stack[2].m_obj;
lean_object* v_a_1571_ = stack[3].m_obj;
lean_object* v_a_1572_ = stack[4].m_obj;
lean_object* v_a_1573_ = stack[5].m_obj;
lean_object* v_a_1574_ = stack[6].m_obj;
lean_object* v_res_1662_;
v_res_1662_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
stack->m_obj
 = v_res_1662_;
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1663_, lean_object* v_xs_1664_, uint8_t v___y_1665_, uint8_t v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1663_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = 1;
v___x_1676_ = l_Lean_Meta_mkLambdaFVars(v_xs_1664_, v_a_1674_, v___y_1665_, v___y_1665_, v___y_1665_, v___y_1665_, v___x_1675_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
return v___x_1676_;
}
else
{
return v___x_1673_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_visit___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1663_ = stack[0].m_obj;
lean_object* v_xs_1664_ = stack[1].m_obj;
uint8_t v___y_1665_ = stack[2].m_num;
uint8_t v___y_1666_ = stack[3].m_num;
lean_object* v___y_1667_ = stack[4].m_obj;
lean_object* v___y_1668_ = stack[5].m_obj;
lean_object* v___y_1669_ = stack[6].m_obj;
lean_object* v___y_1670_ = stack[7].m_obj;
lean_object* v___y_1671_ = stack[8].m_obj;
lean_object* v_res_1677_;
v_res_1677_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1663_, v_xs_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
stack->m_obj
 = v_res_1677_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1678_, lean_object* v_xs_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v___y_27751__boxed_1688_; uint8_t v___y_27752__boxed_1689_; lean_object* v_res_1690_; 
v___y_27751__boxed_1688_ = lean_unbox(v___y_1680_);
v___y_27752__boxed_1689_ = lean_unbox(v___y_1681_);
v_res_1690_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1678_, v_xs_1679_, v___y_27751__boxed_1688_, v___y_27752__boxed_1689_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v_xs_1679_);
return v_res_1690_;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1691_, lean_object* v___f_1692_, lean_object* v_xs_1693_, lean_object* v_b_1694_, uint8_t v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_box(v___y_1691_);
lean_inc_ref(v_xs_1693_);
v___f_1703_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1703_, 0, v_b_1694_);
lean_closure_set(v___f_1703_, 1, v_xs_1693_);
lean_closure_set(v___f_1703_, 2, v___x_1702_);
v___x_1704_ = lean_box(v___y_1695_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
v___x_1705_ = lean_apply_9(v___f_1692_, v_xs_1693_, v___f_1703_, v___x_1704_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, lean_box(0));
return v___x_1705_;
}
}
LEAN_EXPORT void l_Lean_Meta_AbstractNestedProofs_visit___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1691_ = stack[0].m_num;
lean_object* v___f_1692_ = stack[1].m_obj;
lean_object* v_xs_1693_ = stack[2].m_obj;
lean_object* v_b_1694_ = stack[3].m_obj;
uint8_t v___y_1695_ = stack[4].m_num;
lean_object* v___y_1696_ = stack[5].m_obj;
lean_object* v___y_1697_ = stack[6].m_obj;
lean_object* v___y_1698_ = stack[7].m_obj;
lean_object* v___y_1699_ = stack[8].m_obj;
lean_object* v___y_1700_ = stack[9].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_1691_, v___f_1692_, v_xs_1693_, v_b_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1707_, lean_object* v_i_1708_, lean_object* v_bs_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; uint8_t v___y_27791__boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1707_);
lean_dec(v_sz_1707_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1708_);
lean_dec(v_i_1708_);
v___y_27791__boxed_1719_ = lean_unbox(v___y_1710_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1709_, v___y_27791__boxed_1719_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___y_27812__boxed_1731_; lean_object* v_res_1732_; 
v___y_27812__boxed_1731_ = lean_unbox(v___y_1724_);
v_res_1732_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_x_1721_, v_x_1722_, v_x_1723_, v___y_27812__boxed_1731_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_as_1733_, lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
size_t v_sz_boxed_1744_; size_t v_i_boxed_1745_; uint8_t v___y_27835__boxed_1746_; lean_object* v_res_1747_; 
v_sz_boxed_1744_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v___y_27835__boxed_1746_ = lean_unbox(v___y_1737_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_as_1733_, v_sz_boxed_1744_, v_i_boxed_1745_, v_b_1736_, v___y_27835__boxed_1746_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v_as_1733_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_x_1749_, v_x_1750_, v_x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1753_, lean_object* v_m_1754_, lean_object* v_a_1755_, lean_object* v_b_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_m_1754_, v_a_1755_, v_b_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b2_1758_, lean_object* v_m_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1759_, v_a_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_00_u03b2_1762_, lean_object* v_m_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_00_u03b2_1762_, v_m_1763_, v_a_1764_);
lean_dec_ref(v_a_1764_);
lean_dec_ref(v_m_1763_);
return v_res_1765_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1766_, lean_object* v_x_1767_, size_t v_x_1768_, size_t v_x_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_1767_, v_x_1768_, v_x_1769_, v_x_1770_, v_x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1767_ = stack[1].m_obj;
size_t v_x_1768_ = stack[2].m_num;
size_t v_x_1769_ = stack[3].m_num;
lean_object* v_x_1770_ = stack[4].m_obj;
lean_object* v_x_1771_ = stack[5].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_box(0), v_x_1767_, v_x_1768_, v_x_1769_, v_x_1770_, v_x_1771_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
size_t v_x_28775__boxed_1780_; size_t v_x_28776__boxed_1781_; lean_object* v_res_1782_; 
v_x_28775__boxed_1780_ = lean_unbox_usize(v_x_1776_);
lean_dec(v_x_1776_);
v_x_28776__boxed_1781_ = lean_unbox_usize(v_x_1777_);
lean_dec(v_x_1777_);
v_res_1782_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1774_, v_x_1775_, v_x_28775__boxed_1780_, v_x_28776__boxed_1781_, v_x_1778_, v_x_1779_);
return v_res_1782_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object* v_00_u03b2_1783_, lean_object* v_a_1784_, lean_object* v_x_1785_){
_start:
{
uint8_t v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1784_, v_x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1784_ = stack[1].m_obj;
lean_object* v_x_1785_ = stack[2].m_obj;
uint8_t v_res_1787_;
v_res_1787_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_box(0), v_a_1784_, v_x_1785_);
stack->m_num = v_res_1787_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1788_, lean_object* v_a_1789_, lean_object* v_x_1790_){
_start:
{
uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_res_1791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(v_00_u03b2_1788_, v_a_1789_, v_x_1790_);
lean_dec(v_x_1790_);
lean_dec_ref(v_a_1789_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object* v_00_u03b2_1793_, lean_object* v_data_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_data_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object* v_00_u03b2_1796_, lean_object* v_a_1797_, lean_object* v_b_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1797_, v_b_1798_, v_x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object* v_00_u03b2_1801_, lean_object* v_a_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1802_, v_x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_a_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(v_00_u03b2_1805_, v_a_1806_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1808_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(lean_object* v_00_u03b1_1809_, lean_object* v_x_1810_, uint8_t v_isExporting_1811_, uint8_t v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___redArg(v_x_1810_, v_isExporting_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1810_ = stack[1].m_obj;
uint8_t v_isExporting_1811_ = stack[2].m_num;
uint8_t v___y_1812_ = stack[3].m_num;
lean_object* v___y_1813_ = stack[4].m_obj;
lean_object* v___y_1814_ = stack[5].m_obj;
lean_object* v___y_1815_ = stack[6].m_obj;
lean_object* v___y_1816_ = stack[7].m_obj;
lean_object* v___y_1817_ = stack[8].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(lean_box(0), v_x_1810_, v_isExporting_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_x_1822_, lean_object* v_isExporting_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
uint8_t v_isExporting_boxed_1831_; uint8_t v___y_28827__boxed_1832_; lean_object* v_res_1833_; 
v_isExporting_boxed_1831_ = lean_unbox(v_isExporting_1823_);
v___y_28827__boxed_1832_ = lean_unbox(v___y_1824_);
v_res_1833_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_spec__17(v_00_u03b1_1821_, v_x_1822_, v_isExporting_boxed_1831_, v___y_28827__boxed_1832_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
return v_res_1833_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(lean_object* v_00_u03b1_1834_, lean_object* v_x_1835_, uint8_t v_when_1836_, uint8_t v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___redArg(v_x_1835_, v_when_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1835_ = stack[1].m_obj;
uint8_t v_when_1836_ = stack[2].m_num;
uint8_t v___y_1837_ = stack[3].m_num;
lean_object* v___y_1838_ = stack[4].m_obj;
lean_object* v___y_1839_ = stack[5].m_obj;
lean_object* v___y_1840_ = stack[6].m_obj;
lean_object* v___y_1841_ = stack[7].m_obj;
lean_object* v___y_1842_ = stack[8].m_obj;
lean_object* v_res_1845_;
v_res_1845_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(lean_box(0), v_x_1835_, v_when_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
stack->m_obj
 = v_res_1845_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_x_1847_, lean_object* v_when_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v_when_boxed_1856_; uint8_t v___y_28865__boxed_1857_; lean_object* v_res_1858_; 
v_when_boxed_1856_ = lean_unbox(v_when_1848_);
v___y_28865__boxed_1857_ = lean_unbox(v___y_1849_);
v_res_1858_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6_spec__11(v_00_u03b1_1846_, v_x_1847_, v_when_boxed_1856_, v___y_28865__boxed_1857_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1859_, lean_object* v_n_1860_, lean_object* v_k_1861_, lean_object* v_v_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v_n_1860_, v_k_1861_, v_v_1862_);
return v___x_1863_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1864_, size_t v_depth_1865_, lean_object* v_keys_1866_, lean_object* v_vals_1867_, lean_object* v_heq_1868_, lean_object* v_i_1869_, lean_object* v_entries_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_1865_, v_keys_1866_, v_vals_1867_, v_i_1869_, v_entries_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1865_ = stack[1].m_num;
lean_object* v_keys_1866_ = stack[2].m_obj;
lean_object* v_vals_1867_ = stack[3].m_obj;
lean_object* v_i_1869_ = stack[5].m_obj;
lean_object* v_entries_1870_ = stack[6].m_obj;
lean_object* v_res_1872_;
v_res_1872_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_box(0), v_depth_1865_, v_keys_1866_, v_vals_1867_, lean_box(0), v_i_1869_, v_entries_1870_);
stack->m_obj
 = v_res_1872_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1873_, lean_object* v_depth_1874_, lean_object* v_keys_1875_, lean_object* v_vals_1876_, lean_object* v_heq_1877_, lean_object* v_i_1878_, lean_object* v_entries_1879_){
_start:
{
size_t v_depth_boxed_1880_; lean_object* v_res_1881_; 
v_depth_boxed_1880_ = lean_unbox_usize(v_depth_1874_);
lean_dec(v_depth_1874_);
v_res_1881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(v_00_u03b2_1873_, v_depth_boxed_1880_, v_keys_1875_, v_vals_1876_, v_heq_1877_, v_i_1878_, v_entries_1879_);
lean_dec_ref(v_vals_1876_);
lean_dec_ref(v_keys_1875_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_1882_, lean_object* v_i_1883_, lean_object* v_source_1884_, lean_object* v_target_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v_i_1883_, v_source_1884_, v_target_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_x_1888_, v_x_1889_, v_x_1890_, v_x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object* v_00_u03b2_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_x_1894_, v_x_1895_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_unsigned_to_nat(16u);
v___x_1899_ = lean_mk_array(v___x_1898_, v___x_1897_);
return v___x_1899_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1900_);
return v___x_1902_;
}
}
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1903_, uint8_t v_cache_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; 
lean_inc_ref(v_e_1903_);
v___x_1910_ = l_Lean_Meta_isProof(v_e_1903_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1931_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1931_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1931_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_unbox(v_a_1911_);
lean_dec(v_a_1911_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_del_object(v___x_1913_);
v___x_1916_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1917_ = lean_st_mk_ref(v___x_1916_);
v___x_1918_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1903_, v_cache_1904_, v___x_1917_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1927_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_st_ref_get(v___x_1917_);
lean_dec(v___x_1917_);
lean_dec(v___x_1923_);
if (v_isShared_1922_ == 0)
{
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1919_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_dec(v___x_1917_);
return v___x_1918_;
}
}
else
{
lean_object* v___x_1929_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v_e_1903_);
v___x_1929_ = v___x_1913_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_e_1903_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_e_1903_);
v_a_1932_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1910_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1910_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_abstractNestedProofs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1903_ = stack[0].m_obj;
uint8_t v_cache_1904_ = stack[1].m_num;
lean_object* v_a_1905_ = stack[2].m_obj;
lean_object* v_a_1906_ = stack[3].m_obj;
lean_object* v_a_1907_ = stack[4].m_obj;
lean_object* v_a_1908_ = stack[5].m_obj;
lean_object* v_res_1940_;
v_res_1940_ = l_Lean_Meta_abstractNestedProofs(v_e_1903_, v_cache_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
stack->m_obj
 = v_res_1940_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1941_, lean_object* v_cache_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
uint8_t v_cache_boxed_1948_; lean_object* v_res_1949_; 
v_cache_boxed_1948_ = lean_unbox(v_cache_1942_);
v_res_1949_ = l_Lean_Meta_abstractNestedProofs(v_e_1941_, v_cache_boxed_1948_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
return v_res_1949_;
}
}
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AbstractNestedProofs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_AbstractNestedProofs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_AbstractNestedProofs(builtin);
}
#ifdef __cplusplus
}
#endif
