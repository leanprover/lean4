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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0(lean_object* v_proof_1_, uint8_t v___x_2_, lean_object* v_inst_3_, uint8_t v_cache_4_, lean_object* v_type_5_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__0___boxed(lean_object* v_proof_15_, lean_object* v___x_16_, lean_object* v_inst_17_, lean_object* v_cache_18_, lean_object* v_type_19_){
_start:
{
uint8_t v___x_151__boxed_20_; uint8_t v_cache_boxed_21_; lean_object* v_res_22_; 
v___x_151__boxed_20_ = lean_unbox(v___x_16_);
v_cache_boxed_21_ = lean_unbox(v_cache_18_);
v_res_22_ = l_Lean_Meta_abstractProof___redArg___lam__0(v_proof_15_, v___x_151__boxed_20_, v_inst_17_, v_cache_boxed_21_, v_type_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__1(lean_object* v_postprocessType_23_, lean_object* v_toBind_24_, lean_object* v___f_25_, lean_object* v_type_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_apply_1(v_postprocessType_23_, v_type_26_);
v___x_28_ = lean_apply_4(v_toBind_24_, lean_box(0), lean_box(0), v___x_27_, v___f_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2(uint8_t v___x_29_, lean_object* v_inst_30_, lean_object* v_toBind_31_, lean_object* v___f_32_, lean_object* v_type_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = lean_box(v___x_29_);
v___x_35_ = lean_box(v___x_29_);
v___x_36_ = lean_box(v___x_29_);
v___x_37_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___boxed), 9, 4);
lean_closure_set(v___x_37_, 0, v_type_33_);
lean_closure_set(v___x_37_, 1, v___x_34_);
lean_closure_set(v___x_37_, 2, v___x_35_);
lean_closure_set(v___x_37_, 3, v___x_36_);
v___x_38_ = lean_apply_2(v_inst_30_, lean_box(0), v___x_37_);
v___x_39_ = lean_apply_4(v_toBind_31_, lean_box(0), lean_box(0), v___x_38_, v___f_32_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__2___boxed(lean_object* v___x_40_, lean_object* v_inst_41_, lean_object* v_toBind_42_, lean_object* v___f_43_, lean_object* v_type_44_){
_start:
{
uint8_t v___x_181__boxed_45_; lean_object* v_res_46_; 
v___x_181__boxed_45_ = lean_unbox(v___x_40_);
v_res_46_ = l_Lean_Meta_abstractProof___redArg___lam__2(v___x_181__boxed_45_, v_inst_41_, v_toBind_42_, v___f_43_, v_type_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3(lean_object* v_type_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Core_betaReduce(v_type_47_, v___y_50_, v___y_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__3___boxed(lean_object* v_type_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Meta_abstractProof___redArg___lam__3(v_type_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___lam__4(lean_object* v_inst_61_, lean_object* v_toBind_62_, lean_object* v___f_63_, lean_object* v_type_64_){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___f_65_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__3___boxed), 6, 1);
lean_closure_set(v___f_65_, 0, v_type_64_);
v___x_66_ = lean_apply_2(v_inst_61_, lean_box(0), v___f_65_);
v___x_67_ = lean_apply_4(v_toBind_62_, lean_box(0), lean_box(0), v___x_66_, v___f_63_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_proof_72_, uint8_t v_cache_73_, lean_object* v_postprocessType_74_){
_start:
{
lean_object* v_toBind_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_toBind_75_ = lean_ctor_get(v_inst_68_, 1);
lean_inc_n(v_toBind_75_, 4);
lean_inc_ref(v_proof_72_);
v___x_76_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_76_, 0, v_proof_72_);
lean_inc_n(v_inst_69_, 3);
v___x_77_ = lean_apply_2(v_inst_69_, lean_box(0), v___x_76_);
v___x_78_ = 1;
v___x_79_ = lean_box(v___x_78_);
v___x_80_ = lean_box(v_cache_73_);
v___f_81_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_81_, 0, v_proof_72_);
lean_closure_set(v___f_81_, 1, v___x_79_);
lean_closure_set(v___f_81_, 2, v_inst_69_);
lean_closure_set(v___f_81_, 3, v___x_80_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__1), 4, 3);
lean_closure_set(v___f_82_, 0, v_postprocessType_74_);
lean_closure_set(v___f_82_, 1, v_toBind_75_);
lean_closure_set(v___f_82_, 2, v___f_81_);
v___x_83_ = lean_box(v___x_78_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_84_, 0, v___x_83_);
lean_closure_set(v___f_84_, 1, v_inst_69_);
lean_closure_set(v___f_84_, 2, v_toBind_75_);
lean_closure_set(v___f_84_, 3, v___f_82_);
v___f_85_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___redArg___lam__4), 4, 3);
lean_closure_set(v___f_85_, 0, v_inst_69_);
lean_closure_set(v___f_85_, 1, v_toBind_75_);
lean_closure_set(v___f_85_, 2, v___f_84_);
v___x_86_ = l_Lean_withoutExporting___redArg(v_inst_68_, v_inst_70_, v_inst_71_, v___x_77_, v___x_78_);
v___x_87_ = lean_apply_4(v_toBind_75_, lean_box(0), lean_box(0), v___x_86_, v___f_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___redArg___boxed(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_proof_92_, lean_object* v_cache_93_, lean_object* v_postprocessType_94_){
_start:
{
uint8_t v_cache_boxed_95_; lean_object* v_res_96_; 
v_cache_boxed_95_ = lean_unbox(v_cache_93_);
v_res_96_ = l_Lean_Meta_abstractProof___redArg(v_inst_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_proof_92_, v_cache_boxed_95_, v_postprocessType_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof(lean_object* v_m_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_proof_103_, uint8_t v_cache_104_, lean_object* v_postprocessType_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_abstractProof___redArg(v_inst_98_, v_inst_99_, v_inst_100_, v_inst_102_, v_proof_103_, v_cache_104_, v_postprocessType_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___boxed(lean_object* v_m_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_proof_113_, lean_object* v_cache_114_, lean_object* v_postprocessType_115_){
_start:
{
uint8_t v_cache_boxed_116_; lean_object* v_res_117_; 
v_cache_boxed_116_ = lean_unbox(v_cache_114_);
v_res_117_ = l_Lean_Meta_abstractProof(v_m_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_proof_113_, v_cache_boxed_116_, v_postprocessType_115_);
lean_dec_ref(v_inst_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody(lean_object* v_e_118_){
_start:
{
if (lean_obj_tag(v_e_118_) == 6)
{
lean_object* v_body_119_; 
v_body_119_ = lean_ctor_get(v_e_118_, 2);
v_e_118_ = v_body_119_;
goto _start;
}
else
{
lean_inc_ref(v_e_118_);
return v_e_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_getLambdaBody___boxed(lean_object* v_e_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_121_);
lean_dec_ref(v_e_121_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(uint8_t v_a_123_, uint8_t v___x_124_, lean_object* v_as_125_, size_t v_i_126_, size_t v_stop_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_eq(v_i_126_, v_stop_127_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; uint8_t v___y_131_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_129_ = 1;
v___x_135_ = lean_array_uget_borrowed(v_as_125_, v_i_126_);
v___x_136_ = l_Lean_Expr_isAtomic(v___x_135_);
if (v___x_136_ == 0)
{
v___y_131_ = v_a_123_;
goto v___jp_130_;
}
else
{
v___y_131_ = v___x_124_;
goto v___jp_130_;
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
size_t v___x_132_; size_t v___x_133_; 
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_i_126_, v___x_132_);
v_i_126_ = v___x_133_;
goto _start;
}
else
{
return v___x_129_;
}
}
}
else
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object* v_a_138_, lean_object* v___x_139_, lean_object* v_as_140_, lean_object* v_i_141_, lean_object* v_stop_142_){
_start:
{
uint8_t v_a_4013__boxed_143_; uint8_t v___x_4014__boxed_144_; size_t v_i_boxed_145_; size_t v_stop_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_4013__boxed_143_ = lean_unbox(v_a_138_);
v___x_4014__boxed_144_ = lean_unbox(v___x_139_);
v_i_boxed_145_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_146_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_4013__boxed_143_, v___x_4014__boxed_144_, v_as_140_, v_i_boxed_145_, v_stop_boxed_146_);
lean_dec_ref(v_as_140_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(uint8_t v_a_149_, uint8_t v___x_150_, lean_object* v___x_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_152_) == 5)
{
lean_object* v_fn_169_; lean_object* v_arg_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_fn_169_ = lean_ctor_get(v_x_152_, 0);
lean_inc_ref(v_fn_169_);
v_arg_170_ = lean_ctor_get(v_x_152_, 1);
lean_inc_ref(v_arg_170_);
lean_dec_ref_known(v_x_152_, 2);
v___x_171_ = lean_array_set(v_x_153_, v_x_154_, v_arg_170_);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_sub(v_x_154_, v___x_172_);
lean_dec(v_x_154_);
v_x_152_ = v_fn_169_;
v_x_153_ = v___x_171_;
v_x_154_ = v___x_173_;
goto _start;
}
else
{
uint8_t v___x_175_; 
lean_dec(v_x_154_);
v___x_175_ = l_Lean_Expr_isAtomic(v_x_152_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec_ref(v_x_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___x_176_ = lean_box(v_a_149_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
else
{
if (v___x_150_ == 0)
{
if (lean_obj_tag(v_x_152_) == 4)
{
lean_object* v_declName_178_; uint8_t v___x_179_; 
v_declName_178_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_declName_178_);
lean_dec_ref_known(v_x_152_, 2);
v___x_179_ = l_Lean_Environment_contains(v___x_151_, v_declName_178_, v_a_149_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec_ref(v_x_153_);
v___x_180_ = lean_box(v_a_149_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
goto v___jp_156_;
}
}
else
{
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
goto v___jp_156_;
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref(v_x_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v___x_151_);
v___x_182_ = lean_box(v_a_149_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
v___jp_156_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_array_get_size(v_x_153_);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref(v_x_153_);
v___x_160_ = lean_box(v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
else
{
if (v___x_159_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec_ref(v_x_153_);
v___x_162_ = lean_box(v___x_159_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
else
{
size_t v___x_164_; size_t v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_158_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_a_149_, v___x_150_, v_x_153_, v___x_164_, v___x_165_);
lean_dec_ref(v_x_153_);
v___x_167_ = lean_box(v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object* v_a_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
uint8_t v_a_4039__boxed_191_; uint8_t v___x_4040__boxed_192_; lean_object* v_res_193_; 
v_a_4039__boxed_191_ = lean_unbox(v_a_184_);
v___x_4040__boxed_192_ = lean_unbox(v___x_185_);
v_res_193_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_4039__boxed_191_, v___x_4040__boxed_192_, v___x_186_, v_x_187_, v_x_188_, v_x_189_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_201_; lean_object* v_dummy_202_; 
v___x_201_ = lean_box(0);
v_dummy_202_ = l_Lean_Expr_sort___override(v___x_201_);
return v_dummy_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object* v_e_203_, lean_object* v_env_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
lean_inc_ref(v_e_203_);
v___x_210_ = l_Lean_Meta_isProof(v_e_203_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; uint8_t v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v___x_212_ = lean_unbox(v_a_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_env_204_);
lean_dec_ref(v_e_203_);
return v___x_210_;
}
else
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_231_; 
lean_inc(v_a_211_);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_232_);
v___x_214_ = v___x_210_;
v_isShared_215_ = v_isSharedCheck_231_;
goto v_resetjp_213_;
}
else
{
lean_dec(v___x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_231_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3));
v___x_217_ = l_Lean_Expr_isAppOf(v_e_203_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v_dummy_219_; lean_object* v_nargs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_214_);
v___x_218_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_203_);
lean_dec_ref(v_e_203_);
v_dummy_219_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_220_ = l_Lean_Expr_getAppNumArgs(v___x_218_);
lean_inc(v_nargs_220_);
v___x_221_ = lean_mk_array(v_nargs_220_, v_dummy_219_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v_nargs_220_, v___x_222_);
lean_dec(v_nargs_220_);
v___x_224_ = lean_unbox(v_a_211_);
lean_dec(v_a_211_);
v___x_225_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v___x_224_, v___x_217_, v_env_204_, v___x_218_, v___x_221_, v___x_223_);
return v___x_225_;
}
else
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_a_211_);
lean_dec_ref(v_env_204_);
lean_dec_ref(v_e_203_);
v___x_226_ = 0;
v___x_227_ = lean_box(v___x_226_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_227_);
v___x_229_ = v___x_214_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_204_);
lean_dec_ref(v_e_203_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object* v_e_233_, lean_object* v_env_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_233_, v_env_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(lean_object* v___y_241_, uint8_t v_isExporting_242_, lean_object* v___x_243_, lean_object* v___y_244_, lean_object* v___x_245_, lean_object* v_a_x3f_246_){
_start:
{
lean_object* v___x_248_; lean_object* v_env_249_; lean_object* v_nextMacroScope_250_; lean_object* v_ngen_251_; lean_object* v_auxDeclNGen_252_; lean_object* v_traceState_253_; lean_object* v_recordedDeps_254_; lean_object* v_messages_255_; lean_object* v_infoState_256_; lean_object* v_snapshotTasks_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_282_; 
v___x_248_ = lean_st_ref_take(v___y_241_);
v_env_249_ = lean_ctor_get(v___x_248_, 0);
v_nextMacroScope_250_ = lean_ctor_get(v___x_248_, 1);
v_ngen_251_ = lean_ctor_get(v___x_248_, 2);
v_auxDeclNGen_252_ = lean_ctor_get(v___x_248_, 3);
v_traceState_253_ = lean_ctor_get(v___x_248_, 4);
v_recordedDeps_254_ = lean_ctor_get(v___x_248_, 6);
v_messages_255_ = lean_ctor_get(v___x_248_, 7);
v_infoState_256_ = lean_ctor_get(v___x_248_, 8);
v_snapshotTasks_257_ = lean_ctor_get(v___x_248_, 9);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_248_, 5);
lean_dec(v_unused_283_);
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_snapshotTasks_257_);
lean_inc(v_infoState_256_);
lean_inc(v_messages_255_);
lean_inc(v_recordedDeps_254_);
lean_inc(v_traceState_253_);
lean_inc(v_auxDeclNGen_252_);
lean_inc(v_ngen_251_);
lean_inc(v_nextMacroScope_250_);
lean_inc(v_env_249_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_282_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_Environment_setExporting(v_env_249_, v_isExporting_242_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 5, v___x_243_);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_nextMacroScope_250_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_ngen_251_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_auxDeclNGen_252_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_traceState_253_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_recordedDeps_254_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_messages_255_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_infoState_256_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_snapshotTasks_257_);
v___x_263_ = v_reuseFailAlloc_281_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_mctx_266_; lean_object* v_zetaDeltaFVarIds_267_; lean_object* v_postponed_268_; lean_object* v_diag_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
v___x_264_ = lean_st_ref_put(v___y_241_, v___x_263_);
v___x_265_ = lean_st_ref_take(v___y_244_);
v_mctx_266_ = lean_ctor_get(v___x_265_, 0);
v_zetaDeltaFVarIds_267_ = lean_ctor_get(v___x_265_, 2);
v_postponed_268_ = lean_ctor_get(v___x_265_, 3);
v_diag_269_ = lean_ctor_get(v___x_265_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_265_, 1);
lean_dec(v_unused_280_);
v___x_271_ = v___x_265_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_diag_269_);
lean_inc(v_postponed_268_);
lean_inc(v_zetaDeltaFVarIds_267_);
lean_inc(v_mctx_266_);
lean_dec(v___x_265_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_245_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_mctx_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_zetaDeltaFVarIds_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_postponed_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_diag_269_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_st_ref_put(v___y_244_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_273_);
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_284_, lean_object* v_isExporting_285_, lean_object* v___x_286_, lean_object* v___y_287_, lean_object* v___x_288_, lean_object* v_a_x3f_289_, lean_object* v___y_290_){
_start:
{
uint8_t v_isExporting_boxed_291_; lean_object* v_res_292_; 
v_isExporting_boxed_291_ = lean_unbox(v_isExporting_285_);
v_res_292_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_284_, v_isExporting_boxed_291_, v___x_286_, v___y_287_, v___x_288_, v_a_x3f_289_);
lean_dec(v_a_x3f_289_);
lean_dec(v___y_287_);
lean_dec(v___y_284_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_293_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
lean_ctor_set(v___x_299_, 2, v___x_298_);
lean_ctor_set(v___x_299_, 3, v___x_298_);
lean_ctor_set(v___x_299_, 4, v___x_298_);
lean_ctor_set(v___x_299_, 5, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object* v_x_300_, uint8_t v_isExporting_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_env_308_; lean_object* v___x_309_; uint8_t v_isModule_310_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v___x_309_ = l_Lean_Environment_header(v_env_308_);
v_isModule_310_ = lean_ctor_get_uint8(v___x_309_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_309_);
if (v_isModule_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec_ref(v_env_308_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_311_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_311_;
}
else
{
uint8_t v_isExporting_312_; 
v_isExporting_312_ = lean_ctor_get_uint8(v_env_308_, sizeof(void*)*13);
lean_dec_ref(v_env_308_);
if (v_isExporting_301_ == 0)
{
if (v_isExporting_312_ == 0)
{
lean_object* v___x_379_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_379_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_379_;
}
else
{
goto v___jp_313_;
}
}
else
{
if (v_isExporting_312_ == 0)
{
goto v___jp_313_;
}
else
{
lean_object* v___x_380_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_380_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_380_;
}
}
v___jp_313_:
{
lean_object* v___x_314_; lean_object* v_env_315_; lean_object* v_nextMacroScope_316_; lean_object* v_ngen_317_; lean_object* v_auxDeclNGen_318_; lean_object* v_traceState_319_; lean_object* v_recordedDeps_320_; lean_object* v_messages_321_; lean_object* v_infoState_322_; lean_object* v_snapshotTasks_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_377_; 
v___x_314_ = lean_st_ref_take(v___y_305_);
v_env_315_ = lean_ctor_get(v___x_314_, 0);
v_nextMacroScope_316_ = lean_ctor_get(v___x_314_, 1);
v_ngen_317_ = lean_ctor_get(v___x_314_, 2);
v_auxDeclNGen_318_ = lean_ctor_get(v___x_314_, 3);
v_traceState_319_ = lean_ctor_get(v___x_314_, 4);
v_recordedDeps_320_ = lean_ctor_get(v___x_314_, 6);
v_messages_321_ = lean_ctor_get(v___x_314_, 7);
v_infoState_322_ = lean_ctor_get(v___x_314_, 8);
v_snapshotTasks_323_ = lean_ctor_get(v___x_314_, 9);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_314_, 5);
lean_dec(v_unused_378_);
v___x_325_ = v___x_314_;
v_isShared_326_ = v_isSharedCheck_377_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_snapshotTasks_323_);
lean_inc(v_infoState_322_);
lean_inc(v_messages_321_);
lean_inc(v_recordedDeps_320_);
lean_inc(v_traceState_319_);
lean_inc(v_auxDeclNGen_318_);
lean_inc(v_ngen_317_);
lean_inc(v_nextMacroScope_316_);
lean_inc(v_env_315_);
lean_dec(v___x_314_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_377_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = l_Lean_Environment_setExporting(v_env_315_, v_isExporting_301_);
v___x_328_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 5, v___x_328_);
lean_ctor_set(v___x_325_, 0, v___x_327_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_nextMacroScope_316_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_ngen_317_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_auxDeclNGen_318_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_traceState_319_);
lean_ctor_set(v_reuseFailAlloc_376_, 5, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_recordedDeps_320_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v_messages_321_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v_infoState_322_);
lean_ctor_set(v_reuseFailAlloc_376_, 9, v_snapshotTasks_323_);
v___x_330_ = v_reuseFailAlloc_376_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_mctx_333_; lean_object* v_zetaDeltaFVarIds_334_; lean_object* v_postponed_335_; lean_object* v_diag_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_374_; 
v___x_331_ = lean_st_ref_put(v___y_305_, v___x_330_);
v___x_332_ = lean_st_ref_take(v___y_303_);
v_mctx_333_ = lean_ctor_get(v___x_332_, 0);
v_zetaDeltaFVarIds_334_ = lean_ctor_get(v___x_332_, 2);
v_postponed_335_ = lean_ctor_get(v___x_332_, 3);
v_diag_336_ = lean_ctor_get(v___x_332_, 4);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_332_, 1);
lean_dec(v_unused_375_);
v___x_338_ = v___x_332_;
v_isShared_339_ = v_isSharedCheck_374_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_diag_336_);
lean_inc(v_postponed_335_);
lean_inc(v_zetaDeltaFVarIds_334_);
lean_inc(v_mctx_333_);
lean_dec(v___x_332_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_374_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_mctx_333_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_zetaDeltaFVarIds_334_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_postponed_335_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_diag_336_);
v___x_342_ = v_reuseFailAlloc_373_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v_r_344_; 
v___x_343_ = lean_st_ref_put(v___y_303_, v___x_342_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v_r_344_ = lean_apply_5(v_x_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
if (lean_obj_tag(v_r_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_361_; 
v_a_345_ = lean_ctor_get(v_r_344_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_r_344_);
if (v_isSharedCheck_361_ == 0)
{
v___x_347_ = v_r_344_;
v_isShared_348_ = v_isSharedCheck_361_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v_r_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_361_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
lean_inc(v_a_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 1);
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_360_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v___x_351_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_305_, v_isExporting_312_, v___x_328_, v___y_303_, v___x_340_, v___x_350_);
lean_dec_ref(v___x_350_);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_351_, 0);
lean_dec(v_unused_359_);
v___x_353_ = v___x_351_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_dec(v___x_351_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v_a_345_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_345_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_362_ = lean_ctor_get(v_r_344_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v_r_344_, 1);
v___x_363_ = lean_box(0);
v___x_364_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_305_, v_isExporting_312_, v___x_328_, v___y_303_, v___x_340_, v___x_363_);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_372_);
v___x_366_ = v___x_364_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_364_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 1);
lean_ctor_set(v___x_366_, 0, v_a_362_);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_362_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object* v_x_381_, lean_object* v_isExporting_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v_isExporting_boxed_388_; lean_object* v_res_389_; 
v_isExporting_boxed_388_ = lean_unbox(v_isExporting_382_);
v_res_389_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_381_, v_isExporting_boxed_388_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_390_, uint8_t v_when_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
if (v_when_391_ == 0)
{
lean_object* v___x_397_; 
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc(v___y_393_);
lean_inc_ref(v___y_392_);
v___x_397_ = lean_apply_5(v_x_390_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, lean_box(0));
return v___x_397_;
}
else
{
uint8_t v___x_398_; lean_object* v___x_399_; 
v___x_398_ = 0;
v___x_399_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_390_, v___x_398_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_400_, lean_object* v_when_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v_when_boxed_407_; lean_object* v_res_408_; 
v_when_boxed_407_ = lean_unbox(v_when_401_);
v_res_408_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_400_, v_when_boxed_407_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_env_416_; lean_object* v___f_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v___x_415_ = lean_st_ref_get(v_a_413_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_env_416_);
lean_dec(v___x_415_);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_417_, 0, v_e_409_);
lean_closure_set(v___f_417_, 1, v_env_416_);
v___x_418_ = 1;
v___x_419_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_417_, v___x_418_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(uint8_t v_a_427_, uint8_t v___x_428_, lean_object* v___x_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_a_427_, v___x_428_, v___x_429_, v_x_430_, v_x_431_, v_x_432_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v_a_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v_a_4458__boxed_450_; uint8_t v___x_4459__boxed_451_; lean_object* v_res_452_; 
v_a_4458__boxed_450_ = lean_unbox(v_a_439_);
v___x_4459__boxed_451_ = lean_unbox(v___x_440_);
v_res_452_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v_a_4458__boxed_450_, v___x_4459__boxed_451_, v___x_441_, v_x_442_, v_x_443_, v_x_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object* v_00_u03b1_453_, lean_object* v_x_454_, uint8_t v_isExporting_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_454_, v_isExporting_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object* v_00_u03b1_462_, lean_object* v_x_463_, lean_object* v_isExporting_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
uint8_t v_isExporting_boxed_470_; lean_object* v_res_471_; 
v_isExporting_boxed_470_ = lean_unbox(v_isExporting_464_);
v_res_471_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_462_, v_x_463_, v_isExporting_boxed_470_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_472_, lean_object* v_x_473_, uint8_t v_when_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_473_, v_when_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_481_, lean_object* v_x_482_, lean_object* v_when_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v_when_boxed_489_; lean_object* v_res_490_; 
v_when_boxed_489_ = lean_unbox(v_when_483_);
v_res_490_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_481_, v_x_482_, v_when_boxed_489_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(lean_object* v_x_491_, uint8_t v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(v___y_492_);
lean_inc(v___y_493_);
v___x_500_ = lean_apply_7(v_x_491_, v___x_499_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, lean_box(0));
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed(lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___y_26426__boxed_509_; lean_object* v_res_510_; 
v___y_26426__boxed_509_ = lean_unbox(v___y_502_);
v_res_510_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0(v_x_501_, v___y_26426__boxed_509_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_503_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_lctx_511_, lean_object* v_localInsts_512_, lean_object* v_x_513_, uint8_t v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; lean_object* v___f_522_; lean_object* v___x_523_; 
v___x_521_ = lean_box(v___y_514_);
lean_inc(v___y_515_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_522_, 0, v_x_513_);
lean_closure_set(v___f_522_, 1, v___x_521_);
lean_closure_set(v___f_522_, 2, v___y_515_);
v___x_523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_511_, v_localInsts_512_, v___f_522_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_523_) == 0)
{
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg___boxed(lean_object* v_lctx_532_, lean_object* v_localInsts_533_, lean_object* v_x_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___y_26451__boxed_542_; lean_object* v_res_543_; 
v___y_26451__boxed_542_ = lean_unbox(v___y_535_);
v_res_543_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_532_, v_localInsts_533_, v_x_534_, v___y_26451__boxed_542_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b1_544_, lean_object* v_lctx_545_, lean_object* v_localInsts_546_, lean_object* v_x_547_, uint8_t v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_lctx_545_, v_localInsts_546_, v_x_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___boxed(lean_object* v_00_u03b1_556_, lean_object* v_lctx_557_, lean_object* v_localInsts_558_, lean_object* v_x_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
uint8_t v___y_26495__boxed_567_; lean_object* v_res_568_; 
v___y_26495__boxed_567_ = lean_unbox(v___y_560_);
v_res_568_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(v_00_u03b1_556_, v_lctx_557_, v_localInsts_558_, v_x_559_, v___y_26495__boxed_567_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object* v_k_569_, uint8_t v___y_570_, lean_object* v___y_571_, lean_object* v_b_572_, lean_object* v_c_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_box(v___y_570_);
lean_inc(v___y_577_);
lean_inc_ref(v___y_576_);
lean_inc(v___y_575_);
lean_inc_ref(v___y_574_);
lean_inc(v___y_571_);
v___x_580_ = lean_apply_9(v_k_569_, v_b_572_, v_c_573_, v___x_579_, v___y_571_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, lean_box(0));
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object* v_k_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v_b_584_, lean_object* v_c_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v___y_26518__boxed_591_; lean_object* v_res_592_; 
v___y_26518__boxed_591_ = lean_unbox(v___y_582_);
v_res_592_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_k_581_, v___y_26518__boxed_591_, v___y_583_, v_b_584_, v_c_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_583_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object* v_e_593_, lean_object* v_k_594_, uint8_t v_cleanupAnnotations_595_, uint8_t v_preserveNondepLet_596_, uint8_t v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v___f_605_; uint8_t v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_604_ = lean_box(v___y_597_);
lean_inc(v___y_598_);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_605_, 0, v_k_594_);
lean_closure_set(v___f_605_, 1, v___x_604_);
lean_closure_set(v___f_605_, 2, v___y_598_);
v___x_606_ = 1;
v___x_607_ = 0;
v___x_608_ = lean_box(0);
v___x_609_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_593_, v___x_606_, v___x_606_, v_preserveNondepLet_596_, v___x_607_, v___x_608_, v___f_605_, v_cleanupAnnotations_595_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
if (lean_obj_tag(v___x_609_) == 0)
{
return v___x_609_;
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object* v_e_618_, lean_object* v_k_619_, lean_object* v_cleanupAnnotations_620_, lean_object* v_preserveNondepLet_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_629_; uint8_t v_preserveNondepLet_boxed_630_; uint8_t v___y_26543__boxed_631_; lean_object* v_res_632_; 
v_cleanupAnnotations_boxed_629_ = lean_unbox(v_cleanupAnnotations_620_);
v_preserveNondepLet_boxed_630_ = lean_unbox(v_preserveNondepLet_621_);
v___y_26543__boxed_631_ = lean_unbox(v___y_622_);
v_res_632_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_618_, v_k_619_, v_cleanupAnnotations_boxed_629_, v_preserveNondepLet_boxed_630_, v___y_26543__boxed_631_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_00_u03b1_633_, lean_object* v_e_634_, lean_object* v_k_635_, uint8_t v_cleanupAnnotations_636_, uint8_t v_preserveNondepLet_637_, uint8_t v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_634_, v_k_635_, v_cleanupAnnotations_636_, v_preserveNondepLet_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_00_u03b1_646_, lean_object* v_e_647_, lean_object* v_k_648_, lean_object* v_cleanupAnnotations_649_, lean_object* v_preserveNondepLet_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_658_; uint8_t v_preserveNondepLet_boxed_659_; uint8_t v___y_26593__boxed_660_; lean_object* v_res_661_; 
v_cleanupAnnotations_boxed_658_ = lean_unbox(v_cleanupAnnotations_649_);
v_preserveNondepLet_boxed_659_ = lean_unbox(v_preserveNondepLet_650_);
v___y_26593__boxed_660_ = lean_unbox(v___y_651_);
v_res_661_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_646_, v_e_647_, v_k_648_, v_cleanupAnnotations_boxed_658_, v_preserveNondepLet_boxed_659_, v___y_26593__boxed_660_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_type_662_, lean_object* v_k_663_, uint8_t v_cleanupAnnotations_664_, uint8_t v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v___f_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_672_ = lean_box(v___y_665_);
lean_inc(v___y_666_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_673_, 0, v_k_663_);
lean_closure_set(v___f_673_, 1, v___x_672_);
lean_closure_set(v___f_673_, 2, v___y_666_);
v___x_674_ = 0;
v___x_675_ = lean_box(0);
v___x_676_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_674_, v___x_675_, v_type_662_, v___f_673_, v_cleanupAnnotations_664_, v___x_674_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_676_) == 0)
{
return v___x_676_;
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_type_685_, lean_object* v_k_686_, lean_object* v_cleanupAnnotations_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_695_; uint8_t v___y_26616__boxed_696_; lean_object* v_res_697_; 
v_cleanupAnnotations_boxed_695_ = lean_unbox(v_cleanupAnnotations_687_);
v___y_26616__boxed_696_ = lean_unbox(v___y_688_);
v_res_697_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_type_685_, v_k_686_, v_cleanupAnnotations_boxed_695_, v___y_26616__boxed_696_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_698_, lean_object* v_type_699_, lean_object* v_k_700_, uint8_t v_cleanupAnnotations_701_, uint8_t v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_type_699_, v_k_700_, v_cleanupAnnotations_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_710_, lean_object* v_type_711_, lean_object* v_k_712_, lean_object* v_cleanupAnnotations_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_721_; uint8_t v___y_26664__boxed_722_; lean_object* v_res_723_; 
v_cleanupAnnotations_boxed_721_ = lean_unbox(v_cleanupAnnotations_713_);
v___y_26664__boxed_722_ = lean_unbox(v___y_714_);
v_res_723_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_710_, v_type_711_, v_k_712_, v_cleanupAnnotations_boxed_721_, v___y_26664__boxed_722_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_ks_728_; lean_object* v_vs_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_753_; 
v_ks_728_ = lean_ctor_get(v_x_724_, 0);
v_vs_729_ = lean_ctor_get(v_x_724_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_753_ == 0)
{
v___x_731_ = v_x_724_;
v_isShared_732_ = v_isSharedCheck_753_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_vs_729_);
lean_inc(v_ks_728_);
lean_dec(v_x_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_753_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_array_get_size(v_ks_728_);
v___x_734_ = lean_nat_dec_lt(v_x_725_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec(v_x_725_);
v___x_735_ = lean_array_push(v_ks_728_, v_x_726_);
v___x_736_ = lean_array_push(v_vs_729_, v_x_727_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_736_);
lean_ctor_set(v___x_731_, 0, v___x_735_);
v___x_738_ = v___x_731_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v_k_x27_740_; uint8_t v___x_741_; 
v_k_x27_740_ = lean_array_fget_borrowed(v_ks_728_, v_x_725_);
v___x_741_ = l_Lean_instBEqFVarId_beq(v_x_726_, v_k_x27_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_743_; 
if (v_isShared_732_ == 0)
{
v___x_743_ = v___x_731_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_ks_728_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_vs_729_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_x_725_, v___x_744_);
lean_dec(v_x_725_);
v_x_724_ = v___x_743_;
v_x_725_ = v___x_745_;
goto _start;
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = lean_array_fset(v_ks_728_, v_x_725_, v_x_726_);
v___x_749_ = lean_array_fset(v_vs_729_, v_x_725_, v_x_727_);
lean_dec(v_x_725_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_749_);
lean_ctor_set(v___x_731_, 0, v___x_748_);
v___x_751_ = v___x_731_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(lean_object* v_n_754_, lean_object* v_k_755_, lean_object* v_v_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_n_754_, v___x_757_, v_k_755_, v_v_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_x_760_, size_t v_x_761_, size_t v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_es_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v_j_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_es_765_ = lean_ctor_get(v_x_760_, 0);
v___x_766_ = ((size_t)31ULL);
v___x_767_ = lean_usize_land(v_x_761_, v___x_766_);
v_j_768_ = lean_usize_to_nat(v___x_767_);
v___x_769_ = lean_array_get_size(v_es_765_);
v___x_770_ = lean_nat_dec_lt(v_j_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_dec(v_j_768_);
lean_dec(v_x_764_);
lean_dec(v_x_763_);
return v_x_760_;
}
else
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_809_; 
lean_inc_ref(v_es_765_);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_x_760_, 0);
lean_dec(v_unused_810_);
v___x_772_ = v_x_760_;
v_isShared_773_ = v_isSharedCheck_809_;
goto v_resetjp_771_;
}
else
{
lean_dec(v_x_760_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_809_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_v_774_; lean_object* v___x_775_; lean_object* v_xs_x27_776_; lean_object* v___y_778_; 
v_v_774_ = lean_array_fget(v_es_765_, v_j_768_);
v___x_775_ = lean_box(0);
v_xs_x27_776_ = lean_array_fset(v_es_765_, v_j_768_, v___x_775_);
switch(lean_obj_tag(v_v_774_))
{
case 0:
{
lean_object* v_key_783_; lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_794_; 
v_key_783_ = lean_ctor_get(v_v_774_, 0);
v_val_784_ = lean_ctor_get(v_v_774_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_v_774_);
if (v_isSharedCheck_794_ == 0)
{
v___x_786_ = v_v_774_;
v_isShared_787_ = v_isSharedCheck_794_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_inc(v_key_783_);
lean_dec(v_v_774_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_794_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint8_t v___x_788_; 
v___x_788_ = l_Lean_instBEqFVarId_beq(v_x_763_, v_key_783_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_del_object(v___x_786_);
v___x_789_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_783_, v_val_784_, v_x_763_, v_x_764_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___y_778_ = v___x_790_;
goto v___jp_777_;
}
else
{
lean_object* v___x_792_; 
lean_dec(v_val_784_);
lean_dec(v_key_783_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v_x_764_);
lean_ctor_set(v___x_786_, 0, v_x_763_);
v___x_792_ = v___x_786_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_x_763_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_x_764_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v___y_778_ = v___x_792_;
goto v___jp_777_;
}
}
}
}
case 1:
{
lean_object* v_node_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_807_; 
v_node_795_ = lean_ctor_get(v_v_774_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_v_774_);
if (v_isSharedCheck_807_ == 0)
{
v___x_797_ = v_v_774_;
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_node_795_);
lean_dec(v_v_774_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_799_ = ((size_t)5ULL);
v___x_800_ = lean_usize_shift_right(v_x_761_, v___x_799_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_x_762_, v___x_801_);
v___x_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_node_795_, v___x_800_, v___x_802_, v_x_763_, v_x_764_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_803_);
v___x_805_ = v___x_797_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v___y_778_ = v___x_805_;
goto v___jp_777_;
}
}
}
default: 
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_x_763_);
lean_ctor_set(v___x_808_, 1, v_x_764_);
v___y_778_ = v___x_808_;
goto v___jp_777_;
}
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_array_fset(v_xs_x27_776_, v_j_768_, v___y_778_);
lean_dec(v_j_768_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_779_);
v___x_781_ = v___x_772_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
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
lean_object* v_ks_811_; lean_object* v_vs_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_830_; 
v_ks_811_ = lean_ctor_get(v_x_760_, 0);
v_vs_812_ = lean_ctor_get(v_x_760_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_830_ == 0)
{
v___x_814_ = v_x_760_;
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_vs_812_);
lean_inc(v_ks_811_);
lean_dec(v_x_760_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_ks_811_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_vs_812_);
v___x_817_ = v_reuseFailAlloc_829_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v_newNode_818_; size_t v___x_819_; uint8_t v___x_820_; 
v_newNode_818_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v___x_817_, v_x_763_, v_x_764_);
v___x_819_ = ((size_t)7ULL);
v___x_820_ = lean_usize_dec_le(v___x_819_, v_x_762_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_821_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_818_);
v___x_822_ = lean_unsigned_to_nat(4u);
v___x_823_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
if (v___x_823_ == 0)
{
lean_object* v_ks_824_; lean_object* v_vs_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_ks_824_ = lean_ctor_get(v_newNode_818_, 0);
lean_inc_ref(v_ks_824_);
v_vs_825_ = lean_ctor_get(v_newNode_818_, 1);
lean_inc_ref(v_vs_825_);
lean_dec_ref(v_newNode_818_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___closed__0);
v___x_828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_x_762_, v_ks_824_, v_vs_825_, v___x_826_, v___x_827_);
lean_dec_ref(v_vs_825_);
lean_dec_ref(v_ks_824_);
return v___x_828_;
}
else
{
return v_newNode_818_;
}
}
else
{
return v_newNode_818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(size_t v_depth_831_, lean_object* v_keys_832_, lean_object* v_vals_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_array_get_size(v_keys_832_);
v___x_837_ = lean_nat_dec_lt(v_i_834_, v___x_836_);
if (v___x_837_ == 0)
{
lean_dec(v_i_834_);
return v_entries_835_;
}
else
{
lean_object* v_k_838_; lean_object* v_v_839_; uint64_t v___x_840_; size_t v_h_841_; size_t v___x_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v_h_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_k_838_ = lean_array_fget_borrowed(v_keys_832_, v_i_834_);
v_v_839_ = lean_array_fget_borrowed(v_vals_833_, v_i_834_);
v___x_840_ = l_Lean_instHashableFVarId_hash(v_k_838_);
v_h_841_ = lean_uint64_to_usize(v___x_840_);
v___x_842_ = ((size_t)5ULL);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_sub(v_depth_831_, v___x_844_);
v___x_846_ = lean_usize_mul(v___x_842_, v___x_845_);
v_h_847_ = lean_usize_shift_right(v_h_841_, v___x_846_);
v___x_848_ = lean_nat_add(v_i_834_, v___x_843_);
lean_dec(v_i_834_);
lean_inc(v_v_839_);
lean_inc(v_k_838_);
v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_entries_835_, v_h_847_, v_depth_831_, v_k_838_, v_v_839_);
v_i_834_ = v___x_848_;
v_entries_835_ = v___x_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_depth_851_, lean_object* v_keys_852_, lean_object* v_vals_853_, lean_object* v_i_854_, lean_object* v_entries_855_){
_start:
{
size_t v_depth_boxed_856_; lean_object* v_res_857_; 
v_depth_boxed_856_ = lean_unbox_usize(v_depth_851_);
lean_dec(v_depth_851_);
v_res_857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_boxed_856_, v_keys_852_, v_vals_853_, v_i_854_, v_entries_855_);
lean_dec_ref(v_vals_853_);
lean_dec_ref(v_keys_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_26764__boxed_863_; size_t v_x_26765__boxed_864_; lean_object* v_res_865_; 
v_x_26764__boxed_863_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_x_26765__boxed_864_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_858_, v_x_26764__boxed_863_, v_x_26765__boxed_864_, v_x_861_, v_x_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
uint64_t v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; 
v___x_869_ = l_Lean_instHashableFVarId_hash(v_x_867_);
v___x_870_ = lean_uint64_to_usize(v___x_869_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_866_, v___x_870_, v___x_871_, v_x_867_, v_x_868_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(lean_object* v_a_873_, lean_object* v_b_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_dec(v_b_874_);
lean_dec_ref(v_a_873_);
return v_x_875_;
}
else
{
lean_object* v_key_876_; lean_object* v_value_877_; lean_object* v_tail_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_890_; 
v_key_876_ = lean_ctor_get(v_x_875_, 0);
v_value_877_ = lean_ctor_get(v_x_875_, 1);
v_tail_878_ = lean_ctor_get(v_x_875_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_890_ == 0)
{
v___x_880_ = v_x_875_;
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_tail_878_);
lean_inc(v_value_877_);
lean_inc(v_key_876_);
lean_dec(v_x_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_ExprStructEq_beq(v_key_876_, v_a_873_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_873_, v_b_874_, v_tail_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v___x_883_);
v___x_885_ = v___x_880_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_key_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_value_877_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v___x_888_; 
lean_dec(v_value_877_);
lean_dec(v_key_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v_b_874_);
lean_ctor_set(v___x_880_, 0, v_a_873_);
v___x_888_ = v___x_880_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_873_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_b_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_tail_878_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(lean_object* v_a_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
uint8_t v___x_893_; 
v___x_893_ = 0;
return v___x_893_;
}
else
{
lean_object* v_key_894_; lean_object* v_tail_895_; uint8_t v___x_896_; 
v_key_894_ = lean_ctor_get(v_x_892_, 0);
v_tail_895_ = lean_ctor_get(v_x_892_, 2);
v___x_896_ = l_Lean_ExprStructEq_beq(v_key_894_, v_a_891_);
if (v___x_896_ == 0)
{
v_x_892_ = v_tail_895_;
goto _start;
}
else
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg___boxed(lean_object* v_a_898_, lean_object* v_x_899_){
_start:
{
uint8_t v_res_900_; lean_object* v_r_901_; 
v_res_900_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_898_, v_x_899_);
lean_dec(v_x_899_);
lean_dec_ref(v_a_898_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
return v_x_902_;
}
else
{
lean_object* v_key_904_; lean_object* v_value_905_; lean_object* v_tail_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_929_; 
v_key_904_ = lean_ctor_get(v_x_903_, 0);
v_value_905_ = lean_ctor_get(v_x_903_, 1);
v_tail_906_ = lean_ctor_get(v_x_903_, 2);
v_isSharedCheck_929_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_929_ == 0)
{
v___x_908_ = v_x_903_;
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_tail_906_);
lean_inc(v_value_905_);
lean_inc(v_key_904_);
lean_dec(v_x_903_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v_fold_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_910_ = lean_array_get_size(v_x_902_);
v___x_911_ = l_Lean_ExprStructEq_hash(v_key_904_);
v___x_912_ = 32ULL;
v___x_913_ = lean_uint64_shift_right(v___x_911_, v___x_912_);
v_fold_914_ = lean_uint64_xor(v___x_911_, v___x_913_);
v___x_915_ = 16ULL;
v___x_916_ = lean_uint64_shift_right(v_fold_914_, v___x_915_);
v___x_917_ = lean_uint64_xor(v_fold_914_, v___x_916_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
v___x_919_ = lean_usize_of_nat(v___x_910_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_sub(v___x_919_, v___x_920_);
v___x_922_ = lean_usize_land(v___x_918_, v___x_921_);
v___x_923_ = lean_array_uget_borrowed(v_x_902_, v___x_922_);
lean_inc(v___x_923_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 2, v___x_923_);
v___x_925_ = v___x_908_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_key_904_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_value_905_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v___x_923_);
v___x_925_ = v_reuseFailAlloc_928_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = lean_array_uset(v_x_902_, v___x_922_, v___x_925_);
v_x_902_ = v___x_926_;
v_x_903_ = v_tail_906_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(lean_object* v_i_930_, lean_object* v_source_931_, lean_object* v_target_932_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_source_931_);
v___x_934_ = lean_nat_dec_lt(v_i_930_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v_source_931_);
lean_dec(v_i_930_);
return v_target_932_;
}
else
{
lean_object* v_es_935_; lean_object* v___x_936_; lean_object* v_source_937_; lean_object* v_target_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_es_935_ = lean_array_fget(v_source_931_, v_i_930_);
v___x_936_ = lean_box(0);
v_source_937_ = lean_array_fset(v_source_931_, v_i_930_, v___x_936_);
v_target_938_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_target_932_, v_es_935_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_i_930_, v___x_939_);
lean_dec(v_i_930_);
v_i_930_ = v___x_940_;
v_source_931_ = v_source_937_;
v_target_932_ = v_target_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(lean_object* v_data_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_nbuckets_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_943_ = lean_array_get_size(v_data_942_);
v___x_944_ = lean_unsigned_to_nat(2u);
v_nbuckets_945_ = lean_nat_mul(v___x_943_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_box(0);
v___x_948_ = lean_mk_array(v_nbuckets_945_, v___x_947_);
v___x_949_ = lean_array_propagate_mark(v_data_942_, v___x_948_);
v___x_950_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v___x_946_, v_data_942_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(lean_object* v_m_951_, lean_object* v_a_952_, lean_object* v_b_953_){
_start:
{
lean_object* v_size_954_; lean_object* v_buckets_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_998_; 
v_size_954_ = lean_ctor_get(v_m_951_, 0);
v_buckets_955_ = lean_ctor_get(v_m_951_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_m_951_);
if (v_isSharedCheck_998_ == 0)
{
v___x_957_ = v_m_951_;
v_isShared_958_ = v_isSharedCheck_998_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_buckets_955_);
lean_inc(v_size_954_);
lean_dec(v_m_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_998_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v_fold_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; lean_object* v_bkt_972_; uint8_t v___x_973_; 
v___x_959_ = lean_array_get_size(v_buckets_955_);
v___x_960_ = l_Lean_ExprStructEq_hash(v_a_952_);
v___x_961_ = 32ULL;
v___x_962_ = lean_uint64_shift_right(v___x_960_, v___x_961_);
v_fold_963_ = lean_uint64_xor(v___x_960_, v___x_962_);
v___x_964_ = 16ULL;
v___x_965_ = lean_uint64_shift_right(v_fold_963_, v___x_964_);
v___x_966_ = lean_uint64_xor(v_fold_963_, v___x_965_);
v___x_967_ = lean_uint64_to_usize(v___x_966_);
v___x_968_ = lean_usize_of_nat(v___x_959_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_sub(v___x_968_, v___x_969_);
v___x_971_ = lean_usize_land(v___x_967_, v___x_970_);
v_bkt_972_ = lean_array_uget_borrowed(v_buckets_955_, v___x_971_);
v___x_973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_952_, v_bkt_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v_size_x27_975_; lean_object* v___x_976_; lean_object* v_buckets_x27_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_974_ = lean_unsigned_to_nat(1u);
v_size_x27_975_ = lean_nat_add(v_size_954_, v___x_974_);
lean_dec(v_size_954_);
lean_inc(v_bkt_972_);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v_a_952_);
lean_ctor_set(v___x_976_, 1, v_b_953_);
lean_ctor_set(v___x_976_, 2, v_bkt_972_);
v_buckets_x27_977_ = lean_array_uset(v_buckets_955_, v___x_971_, v___x_976_);
v___x_978_ = lean_unsigned_to_nat(4u);
v___x_979_ = lean_nat_mul(v_size_x27_975_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(3u);
v___x_981_ = lean_nat_div(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_array_get_size(v_buckets_x27_977_);
v___x_983_ = lean_nat_dec_le(v___x_981_, v___x_982_);
lean_dec(v___x_981_);
if (v___x_983_ == 0)
{
lean_object* v_val_984_; lean_object* v___x_986_; 
v_val_984_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_buckets_x27_977_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_val_984_);
lean_ctor_set(v___x_957_, 0, v_size_x27_975_);
v___x_986_ = v___x_957_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_size_x27_975_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_val_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v___x_989_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_buckets_x27_977_);
lean_ctor_set(v___x_957_, 0, v_size_x27_975_);
v___x_989_ = v___x_957_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_size_x27_975_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_buckets_x27_977_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v___x_991_; lean_object* v_buckets_x27_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_inc(v_bkt_972_);
v___x_991_ = lean_box(0);
v_buckets_x27_992_ = lean_array_uset(v_buckets_955_, v___x_971_, v___x_991_);
v___x_993_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_952_, v_b_953_, v_bkt_972_);
v___x_994_ = lean_array_uset(v_buckets_x27_992_, v___x_971_, v___x_993_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_994_);
v___x_996_ = v___x_957_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_size_954_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(lean_object* v_a_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
else
{
lean_object* v_key_1002_; lean_object* v_value_1003_; lean_object* v_tail_1004_; uint8_t v___x_1005_; 
v_key_1002_ = lean_ctor_get(v_x_1000_, 0);
v_value_1003_ = lean_ctor_get(v_x_1000_, 1);
v_tail_1004_ = lean_ctor_get(v_x_1000_, 2);
v___x_1005_ = l_Lean_ExprStructEq_beq(v_key_1002_, v_a_999_);
if (v___x_1005_ == 0)
{
v_x_1000_ = v_tail_1004_;
goto _start;
}
else
{
lean_object* v___x_1007_; 
lean_inc(v_value_1003_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_value_1003_);
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg___boxed(lean_object* v_a_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1008_, v_x_1009_);
lean_dec(v_x_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_m_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_buckets_1013_; lean_object* v___x_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v_fold_1018_; uint64_t v___x_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_buckets_1013_ = lean_ctor_get(v_m_1011_, 1);
v___x_1014_ = lean_array_get_size(v_buckets_1013_);
v___x_1015_ = l_Lean_ExprStructEq_hash(v_a_1012_);
v___x_1016_ = 32ULL;
v___x_1017_ = lean_uint64_shift_right(v___x_1015_, v___x_1016_);
v_fold_1018_ = lean_uint64_xor(v___x_1015_, v___x_1017_);
v___x_1019_ = 16ULL;
v___x_1020_ = lean_uint64_shift_right(v_fold_1018_, v___x_1019_);
v___x_1021_ = lean_uint64_xor(v_fold_1018_, v___x_1020_);
v___x_1022_ = lean_uint64_to_usize(v___x_1021_);
v___x_1023_ = lean_usize_of_nat(v___x_1014_);
v___x_1024_ = ((size_t)1ULL);
v___x_1025_ = lean_usize_sub(v___x_1023_, v___x_1024_);
v___x_1026_ = lean_usize_land(v___x_1022_, v___x_1025_);
v___x_1027_ = lean_array_uget_borrowed(v_buckets_1013_, v___x_1026_);
v___x_1028_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1012_, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object* v_m_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1029_, v_a_1030_);
lean_dec_ref(v_a_1030_);
lean_dec_ref(v_m_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(lean_object* v_x_1032_, uint8_t v_isExporting_1033_, uint8_t v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v_env_1042_; lean_object* v___x_1043_; uint8_t v_isModule_1044_; 
v___x_1041_ = lean_st_ref_get(v___y_1039_);
v_env_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc_ref(v_env_1042_);
lean_dec(v___x_1041_);
v___x_1043_ = l_Lean_Environment_header(v_env_1042_);
v_isModule_1044_ = lean_ctor_get_uint8(v___x_1043_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1043_);
if (v_isModule_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref(v_env_1042_);
v___x_1045_ = lean_box(v___y_1034_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
v___x_1046_ = lean_apply_7(v_x_1032_, v___x_1045_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
return v___x_1046_;
}
else
{
uint8_t v_isExporting_1047_; 
v_isExporting_1047_ = lean_ctor_get_uint8(v_env_1042_, sizeof(void*)*13);
lean_dec_ref(v_env_1042_);
if (v_isExporting_1033_ == 0)
{
if (v_isExporting_1047_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_box(v___y_1034_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
v___x_1116_ = lean_apply_7(v_x_1032_, v___x_1115_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
return v___x_1116_;
}
else
{
goto v___jp_1048_;
}
}
else
{
if (v_isExporting_1047_ == 0)
{
goto v___jp_1048_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(v___y_1034_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
v___x_1118_ = lean_apply_7(v_x_1032_, v___x_1117_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
return v___x_1118_;
}
}
v___jp_1048_:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; lean_object* v_nextMacroScope_1051_; lean_object* v_ngen_1052_; lean_object* v_auxDeclNGen_1053_; lean_object* v_traceState_1054_; lean_object* v_recordedDeps_1055_; lean_object* v_messages_1056_; lean_object* v_infoState_1057_; lean_object* v_snapshotTasks_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1113_; 
v___x_1049_ = lean_st_ref_take(v___y_1039_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
v_nextMacroScope_1051_ = lean_ctor_get(v___x_1049_, 1);
v_ngen_1052_ = lean_ctor_get(v___x_1049_, 2);
v_auxDeclNGen_1053_ = lean_ctor_get(v___x_1049_, 3);
v_traceState_1054_ = lean_ctor_get(v___x_1049_, 4);
v_recordedDeps_1055_ = lean_ctor_get(v___x_1049_, 6);
v_messages_1056_ = lean_ctor_get(v___x_1049_, 7);
v_infoState_1057_ = lean_ctor_get(v___x_1049_, 8);
v_snapshotTasks_1058_ = lean_ctor_get(v___x_1049_, 9);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___x_1049_, 5);
lean_dec(v_unused_1114_);
v___x_1060_ = v___x_1049_;
v_isShared_1061_ = v_isSharedCheck_1113_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snapshotTasks_1058_);
lean_inc(v_infoState_1057_);
lean_inc(v_messages_1056_);
lean_inc(v_recordedDeps_1055_);
lean_inc(v_traceState_1054_);
lean_inc(v_auxDeclNGen_1053_);
lean_inc(v_ngen_1052_);
lean_inc(v_nextMacroScope_1051_);
lean_inc(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1113_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1062_ = l_Lean_Environment_setExporting(v_env_1050_, v_isExporting_1033_);
v___x_1063_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 5, v___x_1063_);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1065_ = v___x_1060_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_nextMacroScope_1051_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_ngen_1052_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_auxDeclNGen_1053_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_traceState_1054_);
lean_ctor_set(v_reuseFailAlloc_1112_, 5, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1112_, 6, v_recordedDeps_1055_);
lean_ctor_set(v_reuseFailAlloc_1112_, 7, v_messages_1056_);
lean_ctor_set(v_reuseFailAlloc_1112_, 8, v_infoState_1057_);
lean_ctor_set(v_reuseFailAlloc_1112_, 9, v_snapshotTasks_1058_);
v___x_1065_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_mctx_1068_; lean_object* v_zetaDeltaFVarIds_1069_; lean_object* v_postponed_1070_; lean_object* v_diag_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1110_; 
v___x_1066_ = lean_st_ref_put(v___y_1039_, v___x_1065_);
v___x_1067_ = lean_st_ref_take(v___y_1037_);
v_mctx_1068_ = lean_ctor_get(v___x_1067_, 0);
v_zetaDeltaFVarIds_1069_ = lean_ctor_get(v___x_1067_, 2);
v_postponed_1070_ = lean_ctor_get(v___x_1067_, 3);
v_diag_1071_ = lean_ctor_get(v___x_1067_, 4);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v___x_1067_, 1);
lean_dec(v_unused_1111_);
v___x_1073_ = v___x_1067_;
v_isShared_1074_ = v_isSharedCheck_1110_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_diag_1071_);
lean_inc(v_postponed_1070_);
lean_inc(v_zetaDeltaFVarIds_1069_);
lean_inc(v_mctx_1068_);
lean_dec(v___x_1067_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1110_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_mctx_1068_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_zetaDeltaFVarIds_1069_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_postponed_1070_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_diag_1071_);
v___x_1077_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_r_1080_; 
v___x_1078_ = lean_st_ref_put(v___y_1037_, v___x_1077_);
v___x_1079_ = lean_box(v___y_1034_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
v_r_1080_ = lean_apply_7(v_x_1032_, v___x_1079_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
if (lean_obj_tag(v_r_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1097_; 
v_a_1081_ = lean_ctor_get(v_r_1080_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_r_1080_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1083_ = v_r_1080_;
v_isShared_1084_ = v_isSharedCheck_1097_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v_r_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1097_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
lean_inc(v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 1);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v___x_1087_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_1039_, v_isExporting_1047_, v___x_1063_, v___y_1037_, v___x_1075_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1095_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_a_1081_);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1081_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1098_ = lean_ctor_get(v_r_1080_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_r_1080_, 1);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_1039_, v_isExporting_1047_, v___x_1063_, v___y_1037_, v___x_1075_, v___x_1099_);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___x_1100_, 0);
lean_dec(v_unused_1108_);
v___x_1102_ = v___x_1100_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v___x_1100_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 1);
lean_ctor_set(v___x_1102_, 0, v_a_1098_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1098_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg___boxed(lean_object* v_x_1119_, lean_object* v_isExporting_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v_isExporting_boxed_1128_; uint8_t v___y_27196__boxed_1129_; lean_object* v_res_1130_; 
v_isExporting_boxed_1128_ = lean_unbox(v_isExporting_1120_);
v___y_27196__boxed_1129_ = lean_unbox(v___y_1121_);
v_res_1130_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1119_, v_isExporting_boxed_1128_, v___y_27196__boxed_1129_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(lean_object* v_x_1131_, uint8_t v_when_1132_, uint8_t v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
if (v_when_1132_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(v___y_1133_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v___y_1134_);
v___x_1141_ = lean_apply_7(v_x_1131_, v___x_1140_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1141_;
}
else
{
uint8_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = 0;
v___x_1143_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1131_, v___x_1142_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg___boxed(lean_object* v_x_1144_, lean_object* v_when_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v_when_boxed_1153_; uint8_t v___y_27345__boxed_1154_; lean_object* v_res_1155_; 
v_when_boxed_1153_ = lean_unbox(v_when_1145_);
v___y_27345__boxed_1154_ = lean_unbox(v___y_1146_);
v_res_1155_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v_x_1144_, v_when_boxed_1153_, v___y_27345__boxed_1154_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(lean_object* v_proof_1156_, uint8_t v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
lean_inc(v___y_1162_);
lean_inc_ref(v___y_1161_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
v___x_1164_ = lean_infer_type(v_proof_1156_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed(lean_object* v_proof_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v___y_27374__boxed_1173_; lean_object* v_res_1174_; 
v___y_27374__boxed_1173_ = lean_unbox(v___y_1166_);
v_res_1174_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(v_proof_1165_, v___y_27374__boxed_1173_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_proof_1175_, uint8_t v_cache_1176_, lean_object* v_postprocessType_1177_, uint8_t v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___f_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; 
lean_inc_ref(v_proof_1175_);
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1185_, 0, v_proof_1175_);
v___x_1186_ = 1;
v___x_1187_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v___f_1185_, v___x_1186_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l_Lean_Core_betaReduce(v_a_1188_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = l_Lean_Meta_zetaReduce(v_a_1190_, v___x_1186_, v___x_1186_, v___x_1186_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = lean_box(v___y_1178_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
v___x_1194_ = lean_apply_8(v_postprocessType_1177_, v_a_1192_, v___x_1193_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, lean_box(0));
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; uint8_t v___y_1197_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
if (v_cache_1176_ == 0)
{
v___y_1197_ = v_cache_1176_;
goto v___jp_1196_;
}
else
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_Expr_hasSorry(v_proof_1175_);
if (v___x_1200_ == 0)
{
v___y_1197_ = v_cache_1176_;
goto v___jp_1196_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = 0;
v___y_1197_ = v___x_1201_;
goto v___jp_1196_;
}
}
v___jp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = l_Lean_Meta_mkAuxTheorem(v_a_1195_, v_proof_1175_, v___x_1186_, v___x_1198_, v___y_1197_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1199_;
}
}
else
{
lean_dec_ref(v_proof_1175_);
return v___x_1194_;
}
}
else
{
lean_dec_ref(v_postprocessType_1177_);
lean_dec_ref(v_proof_1175_);
return v___x_1191_;
}
}
else
{
lean_dec_ref(v_postprocessType_1177_);
lean_dec_ref(v_proof_1175_);
return v___x_1189_;
}
}
else
{
lean_dec_ref(v_postprocessType_1177_);
lean_dec_ref(v_proof_1175_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_proof_1202_, lean_object* v_cache_1203_, lean_object* v_postprocessType_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v_cache_boxed_1212_; uint8_t v___y_27397__boxed_1213_; lean_object* v_res_1214_; 
v_cache_boxed_1212_ = lean_unbox(v_cache_1203_);
v___y_27397__boxed_1213_ = lean_unbox(v___y_1205_);
v_res_1214_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_proof_1202_, v_cache_boxed_1212_, v_postprocessType_1204_, v___y_27397__boxed_1213_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_as_1215_, size_t v_sz_1216_, size_t v_i_1217_, lean_object* v_b_1218_, uint8_t v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_a_1227_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_lt(v_i_1217_, v_sz_1216_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_b_1218_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v_localDecl_1245_; lean_object* v___x_1253_; 
v_a_1242_ = lean_array_uget_borrowed(v_as_1215_, v_i_1217_);
v___x_1243_ = l_Lean_Expr_fvarId_x21(v_a_1242_);
lean_inc(v___x_1243_);
v___x_1253_ = l_Lean_FVarId_getDecl___redArg(v___x_1243_, v___y_1221_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = l_Lean_LocalDecl_type(v_a_1254_);
v___x_1256_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1255_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = l_Lean_LocalDecl_setType(v_a_1254_, v_a_1257_);
v___x_1259_ = l_Lean_LocalDecl_value_x3f(v___x_1258_, v___x_1240_);
if (lean_obj_tag(v___x_1259_) == 0)
{
v_localDecl_1245_ = v___x_1258_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1261_; 
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1260_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = l_Lean_LocalDecl_setValue(v___x_1258_, v_a_1262_);
v_localDecl_1245_ = v___x_1263_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v___x_1258_);
lean_dec(v___x_1243_);
lean_dec_ref(v_b_1218_);
v_a_1264_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1261_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_a_1254_);
lean_dec(v___x_1243_);
lean_dec_ref(v_b_1218_);
v_a_1272_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1256_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1256_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v___x_1243_);
lean_dec_ref(v_b_1218_);
v_a_1280_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1253_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1253_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
v___jp_1244_:
{
lean_object* v_fvarIdToDecl_1246_; lean_object* v_decls_1247_; lean_object* v_auxDeclToFullName_1248_; lean_object* v___x_1249_; 
v_fvarIdToDecl_1246_ = lean_ctor_get(v_b_1218_, 0);
v_decls_1247_ = lean_ctor_get(v_b_1218_, 1);
v_auxDeclToFullName_1248_ = lean_ctor_get(v_b_1218_, 2);
lean_inc_ref(v_b_1218_);
v___x_1249_ = lean_local_ctx_find(v_b_1218_, v___x_1243_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_dec_ref(v_localDecl_1245_);
v_a_1227_ = v_b_1218_;
goto v___jp_1226_;
}
else
{
lean_object* v_index_1250_; lean_object* v_fvarId_1251_; lean_object* v___x_1252_; 
lean_inc(v_auxDeclToFullName_1248_);
lean_inc_ref(v_decls_1247_);
lean_inc_ref(v_fvarIdToDecl_1246_);
lean_dec_ref_known(v___x_1249_, 1);
lean_dec_ref(v_b_1218_);
v_index_1250_ = lean_ctor_get(v_localDecl_1245_, 0);
lean_inc(v_index_1250_);
v_fvarId_1251_ = lean_ctor_get(v_localDecl_1245_, 1);
lean_inc_ref(v_localDecl_1245_);
lean_inc(v_fvarId_1251_);
v___x_1252_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_fvarIdToDecl_1246_, v_fvarId_1251_, v_localDecl_1245_);
v___y_1232_ = v_decls_1247_;
v___y_1233_ = v___x_1252_;
v___y_1234_ = v_localDecl_1245_;
v___y_1235_ = v_auxDeclToFullName_1248_;
v___y_1236_ = v_index_1250_;
goto v___jp_1231_;
}
}
}
v___jp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1217_, v___x_1228_);
v_i_1217_ = v___x_1229_;
v_b_1218_ = v_a_1227_;
goto _start;
}
v___jp_1231_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1234_);
v___x_1238_ = l_Lean_PersistentArray_set___redArg(v___y_1232_, v___y_1236_, v___x_1237_);
lean_dec(v___y_1236_);
v___x_1239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1239_, 0, v___y_1233_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_ctor_set(v___x_1239_, 2, v___y_1235_);
v_a_1227_ = v___x_1239_;
goto v___jp_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1288_, lean_object* v_k_1289_, uint8_t v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_lctx_1297_; lean_object* v_localInstances_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_lctx_1297_ = lean_ctor_get(v___y_1292_, 2);
v_localInstances_1298_ = lean_ctor_get(v___y_1292_, 3);
v_sz_1299_ = lean_array_size(v_xs_1288_);
v___x_1300_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1297_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_xs_1288_, v_sz_1299_, v___x_1300_, v_lctx_1297_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
lean_inc_ref(v_localInstances_1298_);
v___x_1303_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_a_1302_, v_localInstances_1298_, v_k_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1303_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_k_1289_);
v_a_1304_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1301_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1301_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1312_, lean_object* v_k_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___y_27508__boxed_1321_; lean_object* v_res_1322_; 
v___y_27508__boxed_1321_ = lean_unbox(v___y_1314_);
v_res_1322_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1312_, v_k_1313_, v___y_27508__boxed_1321_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v_xs_1312_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1324_, lean_object* v___f_1325_, lean_object* v_xs_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v___y_27458__boxed_1335_; uint8_t v___y_27460__boxed_1336_; lean_object* v_res_1337_; 
v___y_27458__boxed_1335_ = lean_unbox(v___y_1324_);
v___y_27460__boxed_1336_ = lean_unbox(v___y_1328_);
v_res_1337_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_27458__boxed_1335_, v___f_1325_, v_xs_1326_, v_b_1327_, v___y_27460__boxed_1336_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1338_, lean_object* v_xs_1339_, uint8_t v___y_1340_, uint8_t v___x_1341_, uint8_t v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1338_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = 1;
v___x_1352_ = l_Lean_Meta_mkForallFVars(v_xs_1339_, v_a_1350_, v___y_1340_, v___x_1341_, v___x_1341_, v___x_1351_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1352_;
}
else
{
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1353_, lean_object* v_xs_1354_, lean_object* v___y_1355_, lean_object* v___x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___y_27494__boxed_1364_; uint8_t v___x_27495__boxed_1365_; uint8_t v___y_27496__boxed_1366_; lean_object* v_res_1367_; 
v___y_27494__boxed_1364_ = lean_unbox(v___y_1355_);
v___x_27495__boxed_1365_ = lean_unbox(v___x_1356_);
v___y_27496__boxed_1366_ = lean_unbox(v___y_1357_);
v_res_1367_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1353_, v_xs_1354_, v___y_27494__boxed_1364_, v___x_27495__boxed_1365_, v___y_27496__boxed_1366_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v_xs_1354_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1368_, uint8_t v___x_1369_, lean_object* v___f_1370_, lean_object* v_xs_1371_, lean_object* v_b_1372_, uint8_t v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1380_ = lean_box(v___y_1368_);
v___x_1381_ = lean_box(v___x_1369_);
lean_inc_ref(v_xs_1371_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1382_, 0, v_b_1372_);
lean_closure_set(v___f_1382_, 1, v_xs_1371_);
lean_closure_set(v___f_1382_, 2, v___x_1380_);
lean_closure_set(v___f_1382_, 3, v___x_1381_);
v___x_1383_ = lean_box(v___y_1373_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
v___x_1384_ = lean_apply_9(v___f_1370_, v_xs_1371_, v___f_1382_, v___x_1383_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, lean_box(0));
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1385_, lean_object* v___x_1386_, lean_object* v___f_1387_, lean_object* v_xs_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v___y_27469__boxed_1397_; uint8_t v___x_27470__boxed_1398_; uint8_t v___y_27472__boxed_1399_; lean_object* v_res_1400_; 
v___y_27469__boxed_1397_ = lean_unbox(v___y_1385_);
v___x_27470__boxed_1398_ = lean_unbox(v___x_1386_);
v___y_27472__boxed_1399_ = lean_unbox(v___y_1390_);
v_res_1400_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_27469__boxed_1397_, v___x_27470__boxed_1398_, v___f_1387_, v_xs_1388_, v_b_1389_, v___y_27472__boxed_1399_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_bs_1403_, uint8_t v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_bs_1403_);
return v___x_1412_;
}
else
{
lean_object* v_v_1413_; lean_object* v___x_1414_; lean_object* v_bs_x27_1415_; lean_object* v___x_1416_; 
v_v_1413_ = lean_array_uget(v_bs_1403_, v_i_1402_);
v___x_1414_ = lean_unsigned_to_nat(0u);
v_bs_x27_1415_ = lean_array_uset(v_bs_1403_, v_i_1402_, v___x_1414_);
v___x_1416_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1413_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; size_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = lean_usize_add(v_i_1402_, v___x_1418_);
v___x_1420_ = lean_array_uset(v_bs_x27_1415_, v_i_1402_, v_a_1417_);
v_i_1402_ = v___x_1419_;
v_bs_1403_ = v___x_1420_;
goto _start;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v_bs_x27_1415_);
v_a_1422_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1416_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1416_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, uint8_t v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 5)
{
lean_object* v_fn_1440_; lean_object* v_arg_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_fn_1440_ = lean_ctor_get(v_x_1430_, 0);
lean_inc_ref(v_fn_1440_);
v_arg_1441_ = lean_ctor_get(v_x_1430_, 1);
lean_inc_ref(v_arg_1441_);
lean_dec_ref_known(v_x_1430_, 2);
v___x_1442_ = lean_array_set(v_x_1431_, v_x_1432_, v_arg_1441_);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_sub(v_x_1432_, v___x_1443_);
lean_dec(v_x_1432_);
v_x_1430_ = v_fn_1440_;
v_x_1431_ = v___x_1442_;
v_x_1432_ = v___x_1444_;
goto _start;
}
else
{
lean_object* v___x_1446_; 
lean_dec(v_x_1432_);
v___x_1446_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1430_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; size_t v_sz_1448_; size_t v___x_1449_; lean_object* v___x_1450_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v_sz_1448_ = lean_array_size(v_x_1431_);
v___x_1449_ = ((size_t)0ULL);
v___x_1450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1448_, v___x_1449_, v_x_1431_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = l_Lean_mkAppN(v_a_1447_, v_a_1451_);
lean_dec(v_a_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1447_);
v_a_1460_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1450_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1450_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_dec_ref(v_x_1431_);
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_a_boxed_1476_; lean_object* v_res_1477_; 
v_a_boxed_1476_ = lean_unbox(v_a_1469_);
v_res_1477_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1468_, v_a_boxed_1476_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1478_, uint8_t v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_a_1487_; lean_object* v___y_1493_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1496_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1497_ = l_Lean_Core_checkSystem(v___x_1496_, v_a_1483_, v_a_1484_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1561_; 
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1497_, 0);
lean_dec(v_unused_1562_);
v___x_1499_ = v___x_1497_;
v_isShared_1500_ = v_isSharedCheck_1561_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v___x_1497_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1561_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
uint8_t v___x_1501_; 
v___x_1501_ = l_Lean_Expr_isAtomic(v_e_1478_);
if (v___x_1501_ == 0)
{
uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = 1;
v___x_1503_ = lean_st_ref_get(v_a_1480_);
v___x_1504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v___x_1503_, v_e_1478_);
lean_dec(v___x_1503_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; 
lean_del_object(v___x_1499_);
lean_inc_ref(v_e_1478_);
v___x_1505_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1478_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; uint8_t v___y_1508_; uint8_t v___x_1542_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1542_ = lean_unbox(v_a_1506_);
lean_dec(v_a_1506_);
if (v___x_1542_ == 0)
{
v___y_1508_ = v___x_1501_;
goto v___jp_1507_;
}
else
{
uint8_t v___x_1543_; 
v___x_1543_ = l_Lean_Expr_hasSorry(v_e_1478_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v___f_1495_);
v___x_1544_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1478_);
v___x_1545_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1478_, v_a_1479_, v___x_1544_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
v___y_1493_ = v___x_1545_;
goto v___jp_1492_;
}
else
{
v___y_1508_ = v___x_1501_;
goto v___jp_1507_;
}
}
v___jp_1507_:
{
switch(lean_obj_tag(v_e_1478_))
{
case 6:
{
lean_object* v___x_1509_; lean_object* v___f_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(v___y_1508_);
v___f_1510_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1510_, 0, v___x_1509_);
lean_closure_set(v___f_1510_, 1, v___f_1495_);
lean_inc_ref(v_e_1478_);
v___x_1511_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_1478_, v___f_1510_, v___y_1508_, v___x_1502_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
v___y_1493_ = v___x_1511_;
goto v___jp_1492_;
}
case 8:
{
lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(v___y_1508_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1513_, 0, v___x_1512_);
lean_closure_set(v___f_1513_, 1, v___f_1495_);
lean_inc_ref(v_e_1478_);
v___x_1514_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_1478_, v___f_1513_, v___y_1508_, v___x_1502_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
v___y_1493_ = v___x_1514_;
goto v___jp_1492_;
}
case 7:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_box(v___y_1508_);
v___x_1516_ = lean_box(v___x_1502_);
v___f_1517_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1517_, 0, v___x_1515_);
lean_closure_set(v___f_1517_, 1, v___x_1516_);
lean_closure_set(v___f_1517_, 2, v___f_1495_);
lean_inc_ref(v_e_1478_);
v___x_1518_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1478_, v___f_1517_, v___y_1508_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
v___y_1493_ = v___x_1518_;
goto v___jp_1492_;
}
case 10:
{
lean_object* v_data_1519_; lean_object* v_expr_1520_; lean_object* v___x_1521_; 
lean_dec_ref(v___f_1495_);
v_data_1519_ = lean_ctor_get(v_e_1478_, 0);
v_expr_1520_ = lean_ctor_get(v_e_1478_, 1);
lean_inc_ref(v_expr_1520_);
v___x_1521_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1520_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; size_t v___x_1523_; size_t v___x_1524_; uint8_t v___x_1525_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = lean_ptr_addr(v_expr_1520_);
v___x_1524_ = lean_ptr_addr(v_a_1522_);
v___x_1525_ = lean_usize_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
lean_inc(v_data_1519_);
v___x_1526_ = l_Lean_Expr_mdata___override(v_data_1519_, v_a_1522_);
v_a_1487_ = v___x_1526_;
goto v___jp_1486_;
}
else
{
lean_dec(v_a_1522_);
lean_inc_ref(v_e_1478_);
v_a_1487_ = v_e_1478_;
goto v___jp_1486_;
}
}
else
{
lean_dec_ref_known(v_e_1478_, 2);
return v___x_1521_;
}
}
case 11:
{
lean_object* v_typeName_1527_; lean_object* v_idx_1528_; lean_object* v_struct_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v___f_1495_);
v_typeName_1527_ = lean_ctor_get(v_e_1478_, 0);
v_idx_1528_ = lean_ctor_get(v_e_1478_, 1);
v_struct_1529_ = lean_ctor_get(v_e_1478_, 2);
lean_inc_ref(v_struct_1529_);
v___x_1530_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1529_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; size_t v___x_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = lean_ptr_addr(v_struct_1529_);
v___x_1533_ = lean_ptr_addr(v_a_1531_);
v___x_1534_ = lean_usize_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_idx_1528_);
lean_inc(v_typeName_1527_);
v___x_1535_ = l_Lean_Expr_proj___override(v_typeName_1527_, v_idx_1528_, v_a_1531_);
v_a_1487_ = v___x_1535_;
goto v___jp_1486_;
}
else
{
lean_dec(v_a_1531_);
lean_inc_ref(v_e_1478_);
v_a_1487_ = v_e_1478_;
goto v___jp_1486_;
}
}
else
{
lean_dec_ref_known(v_e_1478_, 3);
return v___x_1530_;
}
}
case 5:
{
lean_object* v_dummy_1536_; lean_object* v_nargs_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec_ref(v___f_1495_);
v_dummy_1536_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1537_ = l_Lean_Expr_getAppNumArgs(v_e_1478_);
lean_inc(v_nargs_1537_);
v___x_1538_ = lean_mk_array(v_nargs_1537_, v_dummy_1536_);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_sub(v_nargs_1537_, v___x_1539_);
lean_dec(v_nargs_1537_);
lean_inc_ref(v_e_1478_);
v___x_1541_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_e_1478_, v___x_1538_, v___x_1540_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
v___y_1493_ = v___x_1541_;
goto v___jp_1492_;
}
default: 
{
lean_dec_ref(v___f_1495_);
lean_inc_ref(v_e_1478_);
v_a_1487_ = v_e_1478_;
goto v___jp_1486_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v___f_1495_);
lean_dec_ref(v_e_1478_);
v_a_1546_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1505_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1505_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1556_; 
lean_dec_ref(v___f_1495_);
lean_dec_ref(v_e_1478_);
v_val_1554_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v___x_1504_, 1);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v_val_1554_);
v___x_1556_ = v___x_1499_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_val_1554_);
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
lean_object* v___x_1559_; 
lean_dec_ref(v___f_1495_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v_e_1478_);
v___x_1559_ = v___x_1499_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_e_1478_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v___f_1495_);
lean_dec_ref(v_e_1478_);
v_a_1563_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1497_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1497_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = lean_st_ref_take(v_a_1480_);
lean_inc_ref(v_a_1487_);
v___x_1489_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v___x_1488_, v_e_1478_, v_a_1487_);
v___x_1490_ = lean_st_ref_put(v_a_1480_, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_a_1487_);
return v___x_1491_;
}
v___jp_1492_:
{
if (lean_obj_tag(v___y_1493_) == 0)
{
lean_object* v_a_1494_; 
v_a_1494_ = lean_ctor_get(v___y_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___y_1493_, 1);
v_a_1487_ = v_a_1494_;
goto v___jp_1486_;
}
else
{
lean_dec_ref(v_e_1478_);
return v___y_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1571_, lean_object* v_xs_1572_, uint8_t v___y_1573_, uint8_t v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1571_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = 1;
v___x_1584_ = l_Lean_Meta_mkLambdaFVars(v_xs_1572_, v_a_1582_, v___y_1573_, v___y_1573_, v___y_1573_, v___y_1573_, v___x_1583_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1584_;
}
else
{
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1585_, lean_object* v_xs_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v___y_27481__boxed_1595_; uint8_t v___y_27482__boxed_1596_; lean_object* v_res_1597_; 
v___y_27481__boxed_1595_ = lean_unbox(v___y_1587_);
v___y_27482__boxed_1596_ = lean_unbox(v___y_1588_);
v_res_1597_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1585_, v_xs_1586_, v___y_27481__boxed_1595_, v___y_27482__boxed_1596_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v_xs_1586_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1598_, lean_object* v___f_1599_, lean_object* v_xs_1600_, lean_object* v_b_1601_, uint8_t v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1609_ = lean_box(v___y_1598_);
lean_inc_ref(v_xs_1600_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1610_, 0, v_b_1601_);
lean_closure_set(v___f_1610_, 1, v_xs_1600_);
lean_closure_set(v___f_1610_, 2, v___x_1609_);
v___x_1611_ = lean_box(v___y_1602_);
lean_inc(v___y_1607_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
v___x_1612_ = lean_apply_9(v___f_1599_, v_xs_1600_, v___f_1610_, v___x_1611_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, lean_box(0));
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1613_, lean_object* v_i_1614_, lean_object* v_bs_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
size_t v_sz_boxed_1623_; size_t v_i_boxed_1624_; uint8_t v___y_27521__boxed_1625_; lean_object* v_res_1626_; 
v_sz_boxed_1623_ = lean_unbox_usize(v_sz_1613_);
lean_dec(v_sz_1613_);
v_i_boxed_1624_ = lean_unbox_usize(v_i_1614_);
lean_dec(v_i_1614_);
v___y_27521__boxed_1625_ = lean_unbox(v___y_1616_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1623_, v_i_boxed_1624_, v_bs_1615_, v___y_27521__boxed_1625_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v___y_27542__boxed_1637_; lean_object* v_res_1638_; 
v___y_27542__boxed_1637_ = lean_unbox(v___y_1630_);
v_res_1638_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_x_1627_, v_x_1628_, v_x_1629_, v___y_27542__boxed_1637_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_as_1639_, lean_object* v_sz_1640_, lean_object* v_i_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; uint8_t v___y_27565__boxed_1652_; lean_object* v_res_1653_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1640_);
lean_dec(v_sz_1640_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1641_);
lean_dec(v_i_1641_);
v___y_27565__boxed_1652_ = lean_unbox(v___y_1643_);
v_res_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_as_1639_, v_sz_boxed_1650_, v_i_boxed_1651_, v_b_1642_, v___y_27565__boxed_1652_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v_as_1639_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_x_1655_, v_x_1656_, v_x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_00_u03b2_1659_, lean_object* v_m_1660_, lean_object* v_a_1661_, lean_object* v_b_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___redArg(v_m_1660_, v_a_1661_, v_b_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b2_1664_, lean_object* v_m_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_m_1665_, v_a_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_00_u03b2_1668_, lean_object* v_m_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_00_u03b2_1668_, v_m_1669_, v_a_1670_);
lean_dec_ref(v_a_1670_);
lean_dec_ref(v_m_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1672_, lean_object* v_x_1673_, size_t v_x_1674_, size_t v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_x_1673_, v_x_1674_, v_x_1675_, v_x_1676_, v_x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
size_t v_x_28143__boxed_1685_; size_t v_x_28144__boxed_1686_; lean_object* v_res_1687_; 
v_x_28143__boxed_1685_ = lean_unbox_usize(v_x_1681_);
lean_dec(v_x_1681_);
v_x_28144__boxed_1686_ = lean_unbox_usize(v_x_1682_);
lean_dec(v_x_1682_);
v_res_1687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1679_, v_x_1680_, v_x_28143__boxed_1685_, v_x_28144__boxed_1686_, v_x_1683_, v_x_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(lean_object* v_00_u03b2_1688_, lean_object* v_a_1689_, lean_object* v_x_1690_){
_start:
{
uint8_t v___x_1691_; 
v___x_1691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___redArg(v_a_1689_, v_x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1692_, lean_object* v_a_1693_, lean_object* v_x_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__5(v_00_u03b2_1692_, v_a_1693_, v_x_1694_);
lean_dec(v_x_1694_);
lean_dec_ref(v_a_1693_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6(lean_object* v_00_u03b2_1697_, lean_object* v_data_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6___redArg(v_data_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7(lean_object* v_00_u03b2_1700_, lean_object* v_a_1701_, lean_object* v_b_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__7___redArg(v_a_1701_, v_b_1702_, v_x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(lean_object* v_00_u03b2_1705_, lean_object* v_a_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___redArg(v_a_1706_, v_x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1709_, lean_object* v_a_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5_spec__9(v_00_u03b2_1709_, v_a_1710_, v_x_1711_);
lean_dec(v_x_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(lean_object* v_00_u03b1_1713_, lean_object* v_x_1714_, uint8_t v_isExporting_1715_, uint8_t v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1714_, v_isExporting_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_x_1725_, lean_object* v_isExporting_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v_isExporting_boxed_1734_; uint8_t v___y_28175__boxed_1735_; lean_object* v_res_1736_; 
v_isExporting_boxed_1734_ = lean_unbox(v_isExporting_1726_);
v___y_28175__boxed_1735_ = lean_unbox(v___y_1727_);
v_res_1736_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(v_00_u03b1_1724_, v_x_1725_, v_isExporting_boxed_1734_, v___y_28175__boxed_1735_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(lean_object* v_00_u03b1_1737_, lean_object* v_x_1738_, uint8_t v_when_1739_, uint8_t v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v_x_1738_, v_when_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_x_1749_, lean_object* v_when_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v_when_boxed_1758_; uint8_t v___y_28198__boxed_1759_; lean_object* v_res_1760_; 
v_when_boxed_1758_ = lean_unbox(v_when_1750_);
v___y_28198__boxed_1759_ = lean_unbox(v___y_1751_);
v_res_1760_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(v_00_u03b1_1748_, v_x_1749_, v_when_boxed_1758_, v___y_28198__boxed_1759_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1761_, lean_object* v_n_1762_, lean_object* v_k_1763_, lean_object* v_v_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5___redArg(v_n_1762_, v_k_1763_, v_v_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1766_, size_t v_depth_1767_, lean_object* v_keys_1768_, lean_object* v_vals_1769_, lean_object* v_heq_1770_, lean_object* v_i_1771_, lean_object* v_entries_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___redArg(v_depth_1767_, v_keys_1768_, v_vals_1769_, v_i_1771_, v_entries_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1774_, lean_object* v_depth_1775_, lean_object* v_keys_1776_, lean_object* v_vals_1777_, lean_object* v_heq_1778_, lean_object* v_i_1779_, lean_object* v_entries_1780_){
_start:
{
size_t v_depth_boxed_1781_; lean_object* v_res_1782_; 
v_depth_boxed_1781_ = lean_unbox_usize(v_depth_1775_);
lean_dec(v_depth_1775_);
v_res_1782_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__6(v_00_u03b2_1774_, v_depth_boxed_1781_, v_keys_1776_, v_vals_1777_, v_heq_1778_, v_i_1779_, v_entries_1780_);
lean_dec_ref(v_vals_1777_);
lean_dec_ref(v_keys_1776_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_1783_, lean_object* v_i_1784_, lean_object* v_source_1785_, lean_object* v_target_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11___redArg(v_i_1784_, v_source_1785_, v_target_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1_spec__5_spec__11___redArg(v_x_1789_, v_x_1790_, v_x_1791_, v_x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16(lean_object* v_00_u03b2_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4_spec__6_spec__11_spec__16___redArg(v_x_1795_, v_x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_unsigned_to_nat(16u);
v___x_1800_ = lean_mk_array(v___x_1799_, v___x_1798_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1804_, uint8_t v_cache_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1811_; 
lean_inc_ref(v_e_1804_);
v___x_1811_ = l_Lean_Meta_isProof(v_e_1804_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1832_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1832_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1832_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_unbox(v_a_1812_);
lean_dec(v_a_1812_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1814_);
v___x_1817_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1818_ = lean_st_mk_ref(v___x_1817_);
v___x_1819_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1804_, v_cache_1805_, v___x_1818_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_get(v___x_1818_);
lean_dec(v___x_1818_);
lean_dec(v___x_1824_);
if (v_isShared_1823_ == 0)
{
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1820_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
lean_dec(v___x_1818_);
return v___x_1819_;
}
}
else
{
lean_object* v___x_1830_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_e_1804_);
v___x_1830_ = v___x_1814_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_e_1804_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v_e_1804_);
v_a_1833_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1811_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1811_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1841_, lean_object* v_cache_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
uint8_t v_cache_boxed_1848_; lean_object* v_res_1849_; 
v_cache_boxed_1848_ = lean_unbox(v_cache_1842_);
v_res_1849_ = l_Lean_Meta_abstractNestedProofs(v_e_1841_, v_cache_boxed_1848_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
return v_res_1849_;
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
