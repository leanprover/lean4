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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
uint8_t lean_bool_not(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "abstract nested proofs"};
static const lean_object* l_Lean_Meta_AbstractNestedProofs_visit___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractNestedProofs_visit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = l_Lean_Expr_hasSorry(v_proof_1_);
v___x_14_ = lean_bool_not(v___x_13_);
v___y_7_ = v___x_14_;
goto v___jp_6_;
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
uint8_t v___x_145__boxed_20_; uint8_t v_cache_boxed_21_; lean_object* v_res_22_; 
v___x_145__boxed_20_ = lean_unbox(v___x_16_);
v_cache_boxed_21_ = lean_unbox(v_cache_18_);
v_res_22_ = l_Lean_Meta_abstractProof___redArg___lam__0(v_proof_15_, v___x_145__boxed_20_, v_inst_17_, v_cache_boxed_21_, v_type_19_);
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
uint8_t v___x_175__boxed_45_; lean_object* v_res_46_; 
v___x_175__boxed_45_ = lean_unbox(v___x_40_);
v_res_46_ = l_Lean_Meta_abstractProof___redArg___lam__2(v___x_175__boxed_45_, v_inst_41_, v_toBind_42_, v___f_43_, v_type_44_);
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
lean_dec(v_inst_111_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(lean_object* v_as_123_, size_t v_i_124_, size_t v_stop_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = lean_usize_dec_eq(v_i_124_, v_stop_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_array_uget_borrowed(v_as_123_, v_i_124_);
v___x_128_ = l_Lean_Expr_isAtomic(v___x_127_);
v___x_129_ = lean_bool_not(v___x_128_);
if (v___x_129_ == 0)
{
size_t v___x_130_; size_t v___x_131_; 
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_i_124_, v___x_130_);
v_i_124_ = v___x_131_;
goto _start;
}
else
{
return v___x_129_;
}
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0___boxed(lean_object* v_as_134_, lean_object* v_i_135_, lean_object* v_stop_136_){
_start:
{
size_t v_i_boxed_137_; size_t v_stop_boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_i_boxed_137_ = lean_unbox_usize(v_i_135_);
lean_dec(v_i_135_);
v_stop_boxed_138_ = lean_unbox_usize(v_stop_136_);
lean_dec(v_stop_136_);
v_res_139_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_as_134_, v_i_boxed_137_, v_stop_boxed_138_);
lean_dec_ref(v_as_134_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(lean_object* v___x_141_, lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_142_) == 5)
{
lean_object* v_fn_146_; lean_object* v_arg_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_fn_146_ = lean_ctor_get(v_x_142_, 0);
lean_inc_ref(v_fn_146_);
v_arg_147_ = lean_ctor_get(v_x_142_, 1);
lean_inc_ref(v_arg_147_);
lean_dec_ref_known(v_x_142_, 2);
v___x_148_ = lean_array_set(v_x_143_, v_x_144_, v_arg_147_);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_sub(v_x_144_, v___x_149_);
lean_dec(v_x_144_);
v_x_142_ = v_fn_146_;
v_x_143_ = v___x_148_;
v_x_144_ = v___x_150_;
goto _start;
}
else
{
uint8_t v___x_152_; uint8_t v___y_154_; uint8_t v___x_169_; uint8_t v___x_170_; 
lean_dec(v_x_144_);
v___x_152_ = 1;
v___x_169_ = l_Lean_Expr_isAtomic(v_x_142_);
v___x_170_ = lean_bool_not(v___x_169_);
if (v___x_170_ == 0)
{
if (lean_obj_tag(v_x_142_) == 4)
{
lean_object* v_declName_171_; uint8_t v___x_172_; uint8_t v___x_173_; 
v_declName_171_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_declName_171_);
lean_dec_ref_known(v_x_142_, 2);
v___x_172_ = l_Lean_Environment_contains(v___x_141_, v_declName_171_, v___x_152_);
v___x_173_ = lean_bool_not(v___x_172_);
v___y_154_ = v___x_173_;
goto v___jp_153_;
}
else
{
lean_dec_ref(v_x_142_);
lean_dec_ref(v___x_141_);
v___y_154_ = v___x_170_;
goto v___jp_153_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec_ref(v_x_143_);
lean_dec_ref(v_x_142_);
lean_dec_ref(v___x_141_);
v___x_174_ = lean_box(v___x_152_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_array_get_size(v_x_143_);
v___x_157_ = lean_nat_dec_lt(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec_ref(v_x_143_);
v___x_158_ = lean_box(v___y_154_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
else
{
if (v___x_157_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref(v_x_143_);
v___x_160_ = lean_box(v___y_154_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
else
{
size_t v___x_162_; size_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_162_ = ((size_t)0ULL);
v___x_163_ = lean_usize_of_nat(v___x_156_);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__0(v_x_143_, v___x_162_, v___x_163_);
lean_dec_ref(v_x_143_);
v___x_165_ = lean_box(v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v_x_143_);
v___x_167_ = lean_box(v___x_152_);
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg___boxed(lean_object* v___x_176_, lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v___x_176_, v_x_177_, v_x_178_, v_x_179_);
return v_res_181_;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4(void){
_start:
{
lean_object* v___x_189_; lean_object* v_dummy_190_; 
v___x_189_ = lean_box(0);
v_dummy_190_ = l_Lean_Expr_sort___override(v___x_189_);
return v_dummy_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(lean_object* v_e_191_, lean_object* v_env_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; 
lean_inc_ref(v_e_191_);
v___x_198_ = l_Lean_Meta_isProof(v_e_191_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_223_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_223_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_223_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_223_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_unbox(v_a_199_);
lean_dec(v_a_199_);
v___x_204_ = lean_bool_not(v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__3));
v___x_206_ = l_Lean_Expr_isAppOf(v_e_191_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v_dummy_208_; lean_object* v_nargs_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_del_object(v___x_201_);
v___x_207_ = l_Lean_Meta_AbstractNestedProofs_getLambdaBody(v_e_191_);
lean_dec_ref(v_e_191_);
v_dummy_208_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_209_ = l_Lean_Expr_getAppNumArgs(v___x_207_);
lean_inc(v_nargs_209_);
v___x_210_ = lean_mk_array(v_nargs_209_, v_dummy_208_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v_nargs_209_, v___x_211_);
lean_dec(v_nargs_209_);
v___x_213_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v_env_192_, v___x_207_, v___x_210_, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec_ref(v_env_192_);
lean_dec_ref(v_e_191_);
v___x_214_ = lean_box(v___x_204_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_214_);
v___x_216_ = v___x_201_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec_ref(v_env_192_);
lean_dec_ref(v_e_191_);
v___x_218_ = 0;
v___x_219_ = lean_box(v___x_218_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_219_);
v___x_221_ = v___x_201_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_dec_ref(v_env_192_);
lean_dec_ref(v_e_191_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed(lean_object* v_e_224_, lean_object* v_env_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0(v_e_224_, v_env_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(lean_object* v___y_232_, uint8_t v_isExporting_233_, lean_object* v___x_234_, lean_object* v___y_235_, lean_object* v___x_236_, lean_object* v_a_x3f_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_env_240_; lean_object* v_nextMacroScope_241_; lean_object* v_ngen_242_; lean_object* v_auxDeclNGen_243_; lean_object* v_traceState_244_; lean_object* v_messages_245_; lean_object* v_infoState_246_; lean_object* v_snapshotTasks_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_272_; 
v___x_239_ = lean_st_ref_take(v___y_232_);
v_env_240_ = lean_ctor_get(v___x_239_, 0);
v_nextMacroScope_241_ = lean_ctor_get(v___x_239_, 1);
v_ngen_242_ = lean_ctor_get(v___x_239_, 2);
v_auxDeclNGen_243_ = lean_ctor_get(v___x_239_, 3);
v_traceState_244_ = lean_ctor_get(v___x_239_, 4);
v_messages_245_ = lean_ctor_get(v___x_239_, 6);
v_infoState_246_ = lean_ctor_get(v___x_239_, 7);
v_snapshotTasks_247_ = lean_ctor_get(v___x_239_, 8);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_239_, 5);
lean_dec(v_unused_273_);
v___x_249_ = v___x_239_;
v_isShared_250_ = v_isSharedCheck_272_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_snapshotTasks_247_);
lean_inc(v_infoState_246_);
lean_inc(v_messages_245_);
lean_inc(v_traceState_244_);
lean_inc(v_auxDeclNGen_243_);
lean_inc(v_ngen_242_);
lean_inc(v_nextMacroScope_241_);
lean_inc(v_env_240_);
lean_dec(v___x_239_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_272_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_Environment_setExporting(v_env_240_, v_isExporting_233_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 5, v___x_234_);
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_nextMacroScope_241_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_ngen_242_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_auxDeclNGen_243_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_traceState_244_);
lean_ctor_set(v_reuseFailAlloc_271_, 5, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_271_, 6, v_messages_245_);
lean_ctor_set(v_reuseFailAlloc_271_, 7, v_infoState_246_);
lean_ctor_set(v_reuseFailAlloc_271_, 8, v_snapshotTasks_247_);
v___x_253_ = v_reuseFailAlloc_271_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_mctx_256_; lean_object* v_zetaDeltaFVarIds_257_; lean_object* v_postponed_258_; lean_object* v_diag_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v___x_254_ = lean_st_ref_set(v___y_232_, v___x_253_);
v___x_255_ = lean_st_ref_take(v___y_235_);
v_mctx_256_ = lean_ctor_get(v___x_255_, 0);
v_zetaDeltaFVarIds_257_ = lean_ctor_get(v___x_255_, 2);
v_postponed_258_ = lean_ctor_get(v___x_255_, 3);
v_diag_259_ = lean_ctor_get(v___x_255_, 4);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v___x_255_, 1);
lean_dec(v_unused_270_);
v___x_261_ = v___x_255_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_diag_259_);
lean_inc(v_postponed_258_);
lean_inc(v_zetaDeltaFVarIds_257_);
lean_inc(v_mctx_256_);
lean_dec(v___x_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_236_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_mctx_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_zetaDeltaFVarIds_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_postponed_258_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_diag_259_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_st_ref_set(v___y_235_, v___x_264_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_274_, lean_object* v_isExporting_275_, lean_object* v___x_276_, lean_object* v___y_277_, lean_object* v___x_278_, lean_object* v_a_x3f_279_, lean_object* v___y_280_){
_start:
{
uint8_t v_isExporting_boxed_281_; lean_object* v_res_282_; 
v_isExporting_boxed_281_ = lean_unbox(v_isExporting_275_);
v_res_282_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_274_, v_isExporting_boxed_281_, v___x_276_, v___y_277_, v___x_278_, v_a_x3f_279_);
lean_dec(v_a_x3f_279_);
lean_dec(v___y_277_);
lean_dec(v___y_274_);
return v_res_282_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_283_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__1);
v___x_289_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
lean_ctor_set(v___x_289_, 3, v___x_288_);
lean_ctor_set(v___x_289_, 4, v___x_288_);
lean_ctor_set(v___x_289_, 5, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(lean_object* v_x_290_, uint8_t v_isExporting_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_env_298_; uint8_t v_isExporting_299_; uint8_t v___y_366_; lean_object* v___x_368_; uint8_t v_isModule_369_; uint8_t v___x_370_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_env_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_env_298_);
lean_dec(v___x_297_);
v_isExporting_299_ = lean_ctor_get_uint8(v_env_298_, sizeof(void*)*8);
v___x_368_ = l_Lean_Environment_header(v_env_298_);
lean_dec_ref(v_env_298_);
v_isModule_369_ = lean_ctor_get_uint8(v___x_368_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_368_);
v___x_370_ = lean_bool_not(v_isModule_369_);
if (v___x_370_ == 0)
{
if (v_isExporting_299_ == 0)
{
if (v_isExporting_291_ == 0)
{
lean_object* v___x_371_; 
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v___x_371_ = lean_apply_5(v_x_290_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
return v___x_371_;
}
else
{
goto v___jp_300_;
}
}
else
{
v___y_366_ = v_isExporting_291_;
goto v___jp_365_;
}
}
else
{
v___y_366_ = v___x_370_;
goto v___jp_365_;
}
v___jp_300_:
{
lean_object* v___x_301_; lean_object* v_env_302_; lean_object* v_nextMacroScope_303_; lean_object* v_ngen_304_; lean_object* v_auxDeclNGen_305_; lean_object* v_traceState_306_; lean_object* v_messages_307_; lean_object* v_infoState_308_; lean_object* v_snapshotTasks_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_363_; 
v___x_301_ = lean_st_ref_take(v___y_295_);
v_env_302_ = lean_ctor_get(v___x_301_, 0);
v_nextMacroScope_303_ = lean_ctor_get(v___x_301_, 1);
v_ngen_304_ = lean_ctor_get(v___x_301_, 2);
v_auxDeclNGen_305_ = lean_ctor_get(v___x_301_, 3);
v_traceState_306_ = lean_ctor_get(v___x_301_, 4);
v_messages_307_ = lean_ctor_get(v___x_301_, 6);
v_infoState_308_ = lean_ctor_get(v___x_301_, 7);
v_snapshotTasks_309_ = lean_ctor_get(v___x_301_, 8);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v___x_301_, 5);
lean_dec(v_unused_364_);
v___x_311_ = v___x_301_;
v_isShared_312_ = v_isSharedCheck_363_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_snapshotTasks_309_);
lean_inc(v_infoState_308_);
lean_inc(v_messages_307_);
lean_inc(v_traceState_306_);
lean_inc(v_auxDeclNGen_305_);
lean_inc(v_ngen_304_);
lean_inc(v_nextMacroScope_303_);
lean_inc(v_env_302_);
lean_dec(v___x_301_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_363_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = l_Lean_Environment_setExporting(v_env_302_, v_isExporting_291_);
v___x_314_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 5, v___x_314_);
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_nextMacroScope_303_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_ngen_304_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_auxDeclNGen_305_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_traceState_306_);
lean_ctor_set(v_reuseFailAlloc_362_, 5, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_362_, 6, v_messages_307_);
lean_ctor_set(v_reuseFailAlloc_362_, 7, v_infoState_308_);
lean_ctor_set(v_reuseFailAlloc_362_, 8, v_snapshotTasks_309_);
v___x_316_ = v_reuseFailAlloc_362_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_mctx_319_; lean_object* v_zetaDeltaFVarIds_320_; lean_object* v_postponed_321_; lean_object* v_diag_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_360_; 
v___x_317_ = lean_st_ref_set(v___y_295_, v___x_316_);
v___x_318_ = lean_st_ref_take(v___y_293_);
v_mctx_319_ = lean_ctor_get(v___x_318_, 0);
v_zetaDeltaFVarIds_320_ = lean_ctor_get(v___x_318_, 2);
v_postponed_321_ = lean_ctor_get(v___x_318_, 3);
v_diag_322_ = lean_ctor_get(v___x_318_, 4);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v___x_318_, 1);
lean_dec(v_unused_361_);
v___x_324_ = v___x_318_;
v_isShared_325_ = v_isSharedCheck_360_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_diag_322_);
lean_inc(v_postponed_321_);
lean_inc(v_zetaDeltaFVarIds_320_);
lean_inc(v_mctx_319_);
lean_dec(v___x_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_360_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_mctx_319_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_zetaDeltaFVarIds_320_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_postponed_321_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v_diag_322_);
v___x_328_ = v_reuseFailAlloc_359_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v_r_330_; 
v___x_329_ = lean_st_ref_set(v___y_293_, v___x_328_);
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v_r_330_ = lean_apply_5(v_x_290_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
if (lean_obj_tag(v_r_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_347_; 
v_a_331_ = lean_ctor_get(v_r_330_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_r_330_);
if (v_isSharedCheck_347_ == 0)
{
v___x_333_ = v_r_330_;
v_isShared_334_ = v_isSharedCheck_347_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v_r_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_347_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
lean_inc(v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 1);
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_346_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v___x_337_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_295_, v_isExporting_299_, v___x_314_, v___y_293_, v___x_326_, v___x_336_);
lean_dec_ref(v___x_336_);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v___x_337_, 0);
lean_dec(v_unused_345_);
v___x_339_ = v___x_337_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_dec(v___x_337_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v_a_331_);
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_331_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_348_ = lean_ctor_get(v_r_330_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v_r_330_, 1);
v___x_349_ = lean_box(0);
v___x_350_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_295_, v_isExporting_299_, v___x_314_, v___y_293_, v___x_326_, v___x_349_);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v___x_350_, 0);
lean_dec(v_unused_358_);
v___x_352_ = v___x_350_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_dec(v___x_350_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v_a_348_);
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_348_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
}
}
v___jp_365_:
{
if (v___y_366_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v___x_367_; 
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
v___x_367_ = lean_apply_5(v_x_290_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___boxed(lean_object* v_x_372_, lean_object* v_isExporting_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v_isExporting_boxed_379_; lean_object* v_res_380_; 
v_isExporting_boxed_379_ = lean_unbox(v_isExporting_373_);
v_res_380_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_372_, v_isExporting_boxed_379_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(lean_object* v_x_381_, uint8_t v_when_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
if (v_when_382_ == 0)
{
lean_object* v___x_388_; 
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
v___x_388_ = lean_apply_5(v_x_381_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, lean_box(0));
return v___x_388_;
}
else
{
uint8_t v___x_389_; lean_object* v___x_390_; 
v___x_389_ = 0;
v___x_390_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_381_, v___x_389_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg___boxed(lean_object* v_x_391_, lean_object* v_when_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
uint8_t v_when_boxed_398_; lean_object* v_res_399_; 
v_when_boxed_398_ = lean_unbox(v_when_392_);
v_res_399_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_391_, v_when_boxed_398_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* v_e_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v_env_407_; lean_object* v___f_408_; uint8_t v___x_409_; lean_object* v___x_410_; 
v___x_406_ = lean_st_ref_get(v_a_404_);
v_env_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc_ref(v_env_407_);
lean_dec(v___x_406_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___boxed), 7, 2);
lean_closure_set(v___f_408_, 0, v_e_400_);
lean_closure_set(v___f_408_, 1, v_env_407_);
v___x_409_ = 1;
v___x_410_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v___f_408_, v___x_409_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___boxed(lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(lean_object* v___x_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___redArg(v___x_418_, v_x_419_, v_x_420_, v_x_421_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1___boxed(lean_object* v___x_428_, lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__1(v___x_428_, v_x_429_, v_x_430_, v_x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(lean_object* v_00_u03b1_438_, lean_object* v_x_439_, uint8_t v_isExporting_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg(v_x_439_, v_isExporting_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___boxed(lean_object* v_00_u03b1_447_, lean_object* v_x_448_, lean_object* v_isExporting_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
uint8_t v_isExporting_boxed_455_; lean_object* v_res_456_; 
v_isExporting_boxed_455_ = lean_unbox(v_isExporting_449_);
v_res_456_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2(v_00_u03b1_447_, v_x_448_, v_isExporting_boxed_455_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(lean_object* v_00_u03b1_457_, lean_object* v_x_458_, uint8_t v_when_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___redArg(v_x_458_, v_when_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2___boxed(lean_object* v_00_u03b1_466_, lean_object* v_x_467_, lean_object* v_when_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v_when_boxed_474_; lean_object* v_res_475_; 
v_when_boxed_474_ = lean_unbox(v_when_468_);
v_res_475_ = l_Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2(v_00_u03b1_466_, v_x_467_, v_when_boxed_474_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___lam__0(lean_object* v_x_476_, uint8_t v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_box(v___y_477_);
lean_inc(v___y_478_);
v___x_485_ = lean_apply_7(v_x_476_, v___x_484_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, lean_box(0));
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___lam__0___boxed(lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
uint8_t v___y_29350__boxed_494_; lean_object* v_res_495_; 
v___y_29350__boxed_494_ = lean_unbox(v___y_487_);
v_res_495_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___lam__0(v_x_486_, v___y_29350__boxed_494_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_488_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(lean_object* v_lctx_496_, lean_object* v_localInsts_497_, lean_object* v_x_498_, uint8_t v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; 
v___x_506_ = lean_box(v___y_499_);
lean_inc(v___y_500_);
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_507_, 0, v_x_498_);
lean_closure_set(v___f_507_, 1, v___x_506_);
lean_closure_set(v___f_507_, 2, v___y_500_);
v___x_508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_496_, v_localInsts_497_, v___f_507_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_508_) == 0)
{
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg___boxed(lean_object* v_lctx_517_, lean_object* v_localInsts_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___y_29375__boxed_527_; lean_object* v_res_528_; 
v___y_29375__boxed_527_ = lean_unbox(v___y_520_);
v_res_528_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_lctx_517_, v_localInsts_518_, v_x_519_, v___y_29375__boxed_527_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(lean_object* v_00_u03b1_529_, lean_object* v_lctx_530_, lean_object* v_localInsts_531_, lean_object* v_x_532_, uint8_t v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_lctx_530_, v_localInsts_531_, v_x_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___boxed(lean_object* v_00_u03b1_541_, lean_object* v_lctx_542_, lean_object* v_localInsts_543_, lean_object* v_x_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
uint8_t v___y_29419__boxed_552_; lean_object* v_res_553_; 
v___y_29419__boxed_552_ = lean_unbox(v___y_545_);
v_res_553_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5(v_00_u03b1_541_, v_lctx_542_, v_localInsts_543_, v_x_544_, v___y_29419__boxed_552_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(lean_object* v_k_554_, uint8_t v___y_555_, lean_object* v___y_556_, lean_object* v_b_557_, lean_object* v_c_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(v___y_555_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc(v___y_556_);
v___x_565_ = lean_apply_9(v_k_554_, v_b_557_, v_c_558_, v___x_564_, v___y_556_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, lean_box(0));
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed(lean_object* v_k_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v_b_569_, lean_object* v_c_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___y_29442__boxed_576_; lean_object* v_res_577_; 
v___y_29442__boxed_576_ = lean_unbox(v___y_567_);
v_res_577_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0(v_k_566_, v___y_29442__boxed_576_, v___y_568_, v_b_569_, v_c_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(lean_object* v_e_578_, lean_object* v_k_579_, uint8_t v_cleanupAnnotations_580_, uint8_t v_preserveNondepLet_581_, uint8_t v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___f_590_; uint8_t v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = lean_box(v___y_582_);
lean_inc(v___y_583_);
v___f_590_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_590_, 0, v_k_579_);
lean_closure_set(v___f_590_, 1, v___x_589_);
lean_closure_set(v___f_590_, 2, v___y_583_);
v___x_591_ = 1;
v___x_592_ = 0;
v___x_593_ = lean_box(0);
v___x_594_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_578_, v___x_591_, v___x_591_, v_preserveNondepLet_581_, v___x_592_, v___x_593_, v___f_590_, v_cleanupAnnotations_580_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_594_) == 0)
{
return v___x_594_;
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___boxed(lean_object* v_e_603_, lean_object* v_k_604_, lean_object* v_cleanupAnnotations_605_, lean_object* v_preserveNondepLet_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_614_; uint8_t v_preserveNondepLet_boxed_615_; uint8_t v___y_29467__boxed_616_; lean_object* v_res_617_; 
v_cleanupAnnotations_boxed_614_ = lean_unbox(v_cleanupAnnotations_605_);
v_preserveNondepLet_boxed_615_ = lean_unbox(v_preserveNondepLet_606_);
v___y_29467__boxed_616_ = lean_unbox(v___y_607_);
v_res_617_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_603_, v_k_604_, v_cleanupAnnotations_boxed_614_, v_preserveNondepLet_boxed_615_, v___y_29467__boxed_616_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(lean_object* v_00_u03b1_618_, lean_object* v_e_619_, lean_object* v_k_620_, uint8_t v_cleanupAnnotations_621_, uint8_t v_preserveNondepLet_622_, uint8_t v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_619_, v_k_620_, v_cleanupAnnotations_621_, v_preserveNondepLet_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___boxed(lean_object* v_00_u03b1_631_, lean_object* v_e_632_, lean_object* v_k_633_, lean_object* v_cleanupAnnotations_634_, lean_object* v_preserveNondepLet_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_643_; uint8_t v_preserveNondepLet_boxed_644_; uint8_t v___y_29517__boxed_645_; lean_object* v_res_646_; 
v_cleanupAnnotations_boxed_643_ = lean_unbox(v_cleanupAnnotations_634_);
v_preserveNondepLet_boxed_644_ = lean_unbox(v_preserveNondepLet_635_);
v___y_29517__boxed_645_ = lean_unbox(v___y_636_);
v_res_646_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6(v_00_u03b1_631_, v_e_632_, v_k_633_, v_cleanupAnnotations_boxed_643_, v_preserveNondepLet_boxed_644_, v___y_29517__boxed_645_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(lean_object* v_type_647_, lean_object* v_k_648_, uint8_t v_cleanupAnnotations_649_, uint8_t v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___f_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_657_ = lean_box(v___y_650_);
lean_inc(v___y_651_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_658_, 0, v_k_648_);
lean_closure_set(v___f_658_, 1, v___x_657_);
lean_closure_set(v___f_658_, 2, v___y_651_);
v___x_659_ = 0;
v___x_660_ = lean_box(0);
v___x_661_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_659_, v___x_660_, v_type_647_, v___f_658_, v_cleanupAnnotations_649_, v___x_659_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_661_) == 0)
{
return v___x_661_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg___boxed(lean_object* v_type_670_, lean_object* v_k_671_, lean_object* v_cleanupAnnotations_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_680_; uint8_t v___y_29540__boxed_681_; lean_object* v_res_682_; 
v_cleanupAnnotations_boxed_680_ = lean_unbox(v_cleanupAnnotations_672_);
v___y_29540__boxed_681_ = lean_unbox(v___y_673_);
v_res_682_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_type_670_, v_k_671_, v_cleanupAnnotations_boxed_680_, v___y_29540__boxed_681_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(lean_object* v_00_u03b1_683_, lean_object* v_type_684_, lean_object* v_k_685_, uint8_t v_cleanupAnnotations_686_, uint8_t v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_type_684_, v_k_685_, v_cleanupAnnotations_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___boxed(lean_object* v_00_u03b1_695_, lean_object* v_type_696_, lean_object* v_k_697_, lean_object* v_cleanupAnnotations_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_706_; uint8_t v___y_29588__boxed_707_; lean_object* v_res_708_; 
v_cleanupAnnotations_boxed_706_ = lean_unbox(v_cleanupAnnotations_698_);
v___y_29588__boxed_707_ = lean_unbox(v___y_699_);
v_res_708_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7(v_00_u03b1_695_, v_type_696_, v_k_697_, v_cleanupAnnotations_boxed_706_, v___y_29588__boxed_707_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12_spec__17___redArg(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
lean_object* v_ks_713_; lean_object* v_vs_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_738_; 
v_ks_713_ = lean_ctor_get(v_x_709_, 0);
v_vs_714_ = lean_ctor_get(v_x_709_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_738_ == 0)
{
v___x_716_ = v_x_709_;
v_isShared_717_ = v_isSharedCheck_738_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_vs_714_);
lean_inc(v_ks_713_);
lean_dec(v_x_709_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_738_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_get_size(v_ks_713_);
v___x_719_ = lean_nat_dec_lt(v_x_710_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec(v_x_710_);
v___x_720_ = lean_array_push(v_ks_713_, v_x_711_);
v___x_721_ = lean_array_push(v_vs_714_, v_x_712_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_721_);
lean_ctor_set(v___x_716_, 0, v___x_720_);
v___x_723_ = v___x_716_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v_k_x27_725_; uint8_t v___x_726_; 
v_k_x27_725_ = lean_array_fget_borrowed(v_ks_713_, v_x_710_);
v___x_726_ = l_Lean_instBEqFVarId_beq(v_x_711_, v_k_x27_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_728_; 
if (v_isShared_717_ == 0)
{
v___x_728_ = v___x_716_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_ks_713_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_vs_714_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_x_710_, v___x_729_);
lean_dec(v_x_710_);
v_x_709_ = v___x_728_;
v_x_710_ = v___x_730_;
goto _start;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_733_ = lean_array_fset(v_ks_713_, v_x_710_, v_x_711_);
v___x_734_ = lean_array_fset(v_vs_714_, v_x_710_, v_x_712_);
lean_dec(v_x_710_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_734_);
lean_ctor_set(v___x_716_, 0, v___x_733_);
v___x_736_ = v___x_716_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(lean_object* v_n_739_, lean_object* v_k_740_, lean_object* v_v_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_n_739_, v___x_742_, v_k_740_, v_v_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(lean_object* v_x_745_, size_t v_x_746_, size_t v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_745_) == 0)
{
lean_object* v_es_750_; size_t v___x_751_; size_t v___x_752_; lean_object* v_j_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_es_750_ = lean_ctor_get(v_x_745_, 0);
v___x_751_ = ((size_t)31ULL);
v___x_752_ = lean_usize_land(v_x_746_, v___x_751_);
v_j_753_ = lean_usize_to_nat(v___x_752_);
v___x_754_ = lean_array_get_size(v_es_750_);
v___x_755_ = lean_nat_dec_lt(v_j_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec(v_j_753_);
lean_dec(v_x_749_);
lean_dec(v_x_748_);
return v_x_745_;
}
else
{
lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_794_; 
lean_inc_ref(v_es_750_);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_745_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_x_745_, 0);
lean_dec(v_unused_795_);
v___x_757_ = v_x_745_;
v_isShared_758_ = v_isSharedCheck_794_;
goto v_resetjp_756_;
}
else
{
lean_dec(v_x_745_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_794_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_v_759_; lean_object* v___x_760_; lean_object* v_xs_x27_761_; lean_object* v___y_763_; 
v_v_759_ = lean_array_fget(v_es_750_, v_j_753_);
v___x_760_ = lean_box(0);
v_xs_x27_761_ = lean_array_fset(v_es_750_, v_j_753_, v___x_760_);
switch(lean_obj_tag(v_v_759_))
{
case 0:
{
lean_object* v_key_768_; lean_object* v_val_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_779_; 
v_key_768_ = lean_ctor_get(v_v_759_, 0);
v_val_769_ = lean_ctor_get(v_v_759_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_v_759_);
if (v_isSharedCheck_779_ == 0)
{
v___x_771_ = v_v_759_;
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_val_769_);
lean_inc(v_key_768_);
lean_dec(v_v_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
uint8_t v___x_773_; 
v___x_773_ = l_Lean_instBEqFVarId_beq(v_x_748_, v_key_768_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_del_object(v___x_771_);
v___x_774_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_768_, v_val_769_, v_x_748_, v_x_749_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___y_763_ = v___x_775_;
goto v___jp_762_;
}
else
{
lean_object* v___x_777_; 
lean_dec(v_val_769_);
lean_dec(v_key_768_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_x_749_);
lean_ctor_set(v___x_771_, 0, v_x_748_);
v___x_777_ = v___x_771_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_x_748_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_x_749_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v___y_763_ = v___x_777_;
goto v___jp_762_;
}
}
}
}
case 1:
{
lean_object* v_node_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_792_; 
v_node_780_ = lean_ctor_get(v_v_759_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_v_759_);
if (v_isSharedCheck_792_ == 0)
{
v___x_782_ = v_v_759_;
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_node_780_);
lean_dec(v_v_759_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_792_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_784_ = ((size_t)5ULL);
v___x_785_ = lean_usize_shift_right(v_x_746_, v___x_784_);
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_x_747_, v___x_786_);
v___x_788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_node_780_, v___x_785_, v___x_787_, v_x_748_, v_x_749_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_788_);
v___x_790_ = v___x_782_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_763_ = v___x_790_;
goto v___jp_762_;
}
}
}
default: 
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_x_748_);
lean_ctor_set(v___x_793_, 1, v_x_749_);
v___y_763_ = v___x_793_;
goto v___jp_762_;
}
}
v___jp_762_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = lean_array_fset(v_xs_x27_761_, v_j_753_, v___y_763_);
lean_dec(v_j_753_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_764_);
v___x_766_ = v___x_757_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v_ks_796_; lean_object* v_vs_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_817_; 
v_ks_796_ = lean_ctor_get(v_x_745_, 0);
v_vs_797_ = lean_ctor_get(v_x_745_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_745_);
if (v_isSharedCheck_817_ == 0)
{
v___x_799_ = v_x_745_;
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_vs_797_);
lean_inc(v_ks_796_);
lean_dec(v_x_745_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_ks_796_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_vs_797_);
v___x_802_ = v_reuseFailAlloc_816_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v_newNode_803_; uint8_t v___y_805_; size_t v___x_811_; uint8_t v___x_812_; 
v_newNode_803_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v___x_802_, v_x_748_, v_x_749_);
v___x_811_ = ((size_t)7ULL);
v___x_812_ = lean_usize_dec_le(v___x_811_, v_x_747_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_813_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_803_);
v___x_814_ = lean_unsigned_to_nat(4u);
v___x_815_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
lean_dec(v___x_813_);
v___y_805_ = v___x_815_;
goto v___jp_804_;
}
else
{
v___y_805_ = v___x_812_;
goto v___jp_804_;
}
v___jp_804_:
{
if (v___y_805_ == 0)
{
lean_object* v_ks_806_; lean_object* v_vs_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_ks_806_ = lean_ctor_get(v_newNode_803_, 0);
lean_inc_ref(v_ks_806_);
v_vs_807_ = lean_ctor_get(v_newNode_803_, 1);
lean_inc_ref(v_vs_807_);
lean_dec_ref(v_newNode_803_);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___closed__0);
v___x_810_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg(v_x_747_, v_ks_806_, v_vs_807_, v___x_808_, v___x_809_);
lean_dec_ref(v_vs_807_);
lean_dec_ref(v_ks_806_);
return v___x_810_;
}
else
{
return v_newNode_803_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg(size_t v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_i_821_, lean_object* v_entries_822_){
_start:
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = lean_array_get_size(v_keys_819_);
v___x_824_ = lean_nat_dec_lt(v_i_821_, v___x_823_);
if (v___x_824_ == 0)
{
lean_dec(v_i_821_);
return v_entries_822_;
}
else
{
lean_object* v_k_825_; lean_object* v_v_826_; uint64_t v___x_827_; size_t v_h_828_; size_t v___x_829_; lean_object* v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v_h_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_k_825_ = lean_array_fget_borrowed(v_keys_819_, v_i_821_);
v_v_826_ = lean_array_fget_borrowed(v_vals_820_, v_i_821_);
v___x_827_ = l_Lean_instHashableFVarId_hash(v_k_825_);
v_h_828_ = lean_uint64_to_usize(v___x_827_);
v___x_829_ = ((size_t)5ULL);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_sub(v_depth_818_, v___x_831_);
v___x_833_ = lean_usize_mul(v___x_829_, v___x_832_);
v_h_834_ = lean_usize_shift_right(v_h_828_, v___x_833_);
v___x_835_ = lean_nat_add(v_i_821_, v___x_830_);
lean_dec(v_i_821_);
lean_inc(v_v_826_);
lean_inc(v_k_825_);
v___x_836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_entries_822_, v_h_834_, v_depth_818_, v_k_825_, v_v_826_);
v_i_821_ = v___x_835_;
v_entries_822_ = v___x_836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg___boxed(lean_object* v_depth_838_, lean_object* v_keys_839_, lean_object* v_vals_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
size_t v_depth_boxed_843_; lean_object* v_res_844_; 
v_depth_boxed_843_ = lean_unbox_usize(v_depth_838_);
lean_dec(v_depth_838_);
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg(v_depth_boxed_843_, v_keys_839_, v_vals_840_, v_i_841_, v_entries_842_);
lean_dec_ref(v_vals_840_);
lean_dec_ref(v_keys_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg___boxed(lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
size_t v_x_29688__boxed_850_; size_t v_x_29689__boxed_851_; lean_object* v_res_852_; 
v_x_29688__boxed_850_ = lean_unbox_usize(v_x_846_);
lean_dec(v_x_846_);
v_x_29689__boxed_851_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_845_, v_x_29688__boxed_850_, v_x_29689__boxed_851_, v_x_848_, v_x_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
uint64_t v___x_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_856_ = l_Lean_instHashableFVarId_hash(v_x_854_);
v___x_857_ = lean_uint64_to_usize(v___x_856_);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_853_, v___x_857_, v___x_858_, v_x_854_, v_x_855_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(lean_object* v_a_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
else
{
lean_object* v_key_863_; lean_object* v_value_864_; lean_object* v_tail_865_; uint8_t v___x_866_; 
v_key_863_ = lean_ctor_get(v_x_861_, 0);
v_value_864_ = lean_ctor_get(v_x_861_, 1);
v_tail_865_ = lean_ctor_get(v_x_861_, 2);
v___x_866_ = l_Lean_ExprStructEq_beq(v_key_863_, v_a_860_);
if (v___x_866_ == 0)
{
v_x_861_ = v_tail_865_;
goto _start;
}
else
{
lean_object* v___x_868_; 
lean_inc(v_value_864_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v_value_864_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg___boxed(lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_869_, v_x_870_);
lean_dec(v_x_870_);
lean_dec_ref(v_a_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(lean_object* v_m_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_buckets_874_; lean_object* v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v_fold_879_; uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_buckets_874_ = lean_ctor_get(v_m_872_, 1);
v___x_875_ = lean_array_get_size(v_buckets_874_);
v___x_876_ = l_Lean_ExprStructEq_hash(v_a_873_);
v___x_877_ = 32ULL;
v___x_878_ = lean_uint64_shift_right(v___x_876_, v___x_877_);
v_fold_879_ = lean_uint64_xor(v___x_876_, v___x_878_);
v___x_880_ = 16ULL;
v___x_881_ = lean_uint64_shift_right(v_fold_879_, v___x_880_);
v___x_882_ = lean_uint64_xor(v_fold_879_, v___x_881_);
v___x_883_ = lean_uint64_to_usize(v___x_882_);
v___x_884_ = lean_usize_of_nat(v___x_875_);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_sub(v___x_884_, v___x_885_);
v___x_887_ = lean_usize_land(v___x_883_, v___x_886_);
v___x_888_ = lean_array_uget_borrowed(v_buckets_874_, v___x_887_);
v___x_889_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_873_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg___boxed(lean_object* v_m_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_890_, v_a_891_);
lean_dec_ref(v_a_891_);
lean_dec_ref(v_m_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(lean_object* v_x_893_, uint8_t v_isExporting_894_, uint8_t v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; lean_object* v_env_903_; uint8_t v_isExporting_904_; uint8_t v___y_972_; lean_object* v___x_975_; uint8_t v_isModule_976_; uint8_t v___x_977_; 
v___x_902_ = lean_st_ref_get(v___y_900_);
v_env_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc_ref(v_env_903_);
lean_dec(v___x_902_);
v_isExporting_904_ = lean_ctor_get_uint8(v_env_903_, sizeof(void*)*8);
v___x_975_ = l_Lean_Environment_header(v_env_903_);
lean_dec_ref(v_env_903_);
v_isModule_976_ = lean_ctor_get_uint8(v___x_975_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_bool_not(v_isModule_976_);
if (v___x_977_ == 0)
{
if (v_isExporting_904_ == 0)
{
if (v_isExporting_894_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_box(v___y_895_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
v___x_979_ = lean_apply_7(v_x_893_, v___x_978_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, lean_box(0));
return v___x_979_;
}
else
{
goto v___jp_905_;
}
}
else
{
v___y_972_ = v_isExporting_894_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v___x_977_;
goto v___jp_971_;
}
v___jp_905_:
{
lean_object* v___x_906_; lean_object* v_env_907_; lean_object* v_nextMacroScope_908_; lean_object* v_ngen_909_; lean_object* v_auxDeclNGen_910_; lean_object* v_traceState_911_; lean_object* v_messages_912_; lean_object* v_infoState_913_; lean_object* v_snapshotTasks_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_969_; 
v___x_906_ = lean_st_ref_take(v___y_900_);
v_env_907_ = lean_ctor_get(v___x_906_, 0);
v_nextMacroScope_908_ = lean_ctor_get(v___x_906_, 1);
v_ngen_909_ = lean_ctor_get(v___x_906_, 2);
v_auxDeclNGen_910_ = lean_ctor_get(v___x_906_, 3);
v_traceState_911_ = lean_ctor_get(v___x_906_, 4);
v_messages_912_ = lean_ctor_get(v___x_906_, 6);
v_infoState_913_ = lean_ctor_get(v___x_906_, 7);
v_snapshotTasks_914_ = lean_ctor_get(v___x_906_, 8);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v___x_906_, 5);
lean_dec(v_unused_970_);
v___x_916_ = v___x_906_;
v_isShared_917_ = v_isSharedCheck_969_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_snapshotTasks_914_);
lean_inc(v_infoState_913_);
lean_inc(v_messages_912_);
lean_inc(v_traceState_911_);
lean_inc(v_auxDeclNGen_910_);
lean_inc(v_ngen_909_);
lean_inc(v_nextMacroScope_908_);
lean_inc(v_env_907_);
lean_dec(v___x_906_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_969_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_918_ = l_Lean_Environment_setExporting(v_env_907_, v_isExporting_894_);
v___x_919_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__2);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 5, v___x_919_);
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_921_ = v___x_916_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_nextMacroScope_908_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_ngen_909_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_auxDeclNGen_910_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_traceState_911_);
lean_ctor_set(v_reuseFailAlloc_968_, 5, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_968_, 6, v_messages_912_);
lean_ctor_set(v_reuseFailAlloc_968_, 7, v_infoState_913_);
lean_ctor_set(v_reuseFailAlloc_968_, 8, v_snapshotTasks_914_);
v___x_921_ = v_reuseFailAlloc_968_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_mctx_924_; lean_object* v_zetaDeltaFVarIds_925_; lean_object* v_postponed_926_; lean_object* v_diag_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_966_; 
v___x_922_ = lean_st_ref_set(v___y_900_, v___x_921_);
v___x_923_ = lean_st_ref_take(v___y_898_);
v_mctx_924_ = lean_ctor_get(v___x_923_, 0);
v_zetaDeltaFVarIds_925_ = lean_ctor_get(v___x_923_, 2);
v_postponed_926_ = lean_ctor_get(v___x_923_, 3);
v_diag_927_ = lean_ctor_get(v___x_923_, 4);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_923_, 1);
lean_dec(v_unused_967_);
v___x_929_ = v___x_923_;
v_isShared_930_ = v_isSharedCheck_966_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_diag_927_);
lean_inc(v_postponed_926_);
lean_inc(v_zetaDeltaFVarIds_925_);
lean_inc(v_mctx_924_);
lean_dec(v___x_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_966_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___closed__3);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_mctx_924_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_zetaDeltaFVarIds_925_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_postponed_926_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_diag_927_);
v___x_933_ = v_reuseFailAlloc_965_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_r_936_; 
v___x_934_ = lean_st_ref_set(v___y_898_, v___x_933_);
v___x_935_ = lean_box(v___y_895_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
v_r_936_ = lean_apply_7(v_x_893_, v___x_935_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, lean_box(0));
if (lean_obj_tag(v_r_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_953_; 
v_a_937_ = lean_ctor_get(v_r_936_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_r_936_);
if (v_isSharedCheck_953_ == 0)
{
v___x_939_ = v_r_936_;
v_isShared_940_ = v_isSharedCheck_953_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v_r_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_953_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
lean_inc(v_a_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_952_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v___x_943_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_900_, v_isExporting_904_, v___x_919_, v___y_898_, v___x_931_, v___x_942_);
lean_dec_ref(v___x_942_);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_943_, 0);
lean_dec(v_unused_951_);
v___x_945_ = v___x_943_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_dec(v___x_943_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_a_937_);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_937_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_954_ = lean_ctor_get(v_r_936_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v_r_936_, 1);
v___x_955_ = lean_box(0);
v___x_956_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_AbstractNestedProofs_isNonTrivialProof_spec__2_spec__2___redArg___lam__0(v___y_900_, v_isExporting_904_, v___x_919_, v___y_898_, v___x_931_, v___x_955_);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v___x_956_, 0);
lean_dec(v_unused_964_);
v___x_958_ = v___x_956_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_dec(v___x_956_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 1);
lean_ctor_set(v___x_958_, 0, v_a_954_);
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_954_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
}
v___jp_971_:
{
if (v___y_972_ == 0)
{
goto v___jp_905_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_box(v___y_895_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
lean_inc(v___y_896_);
v___x_974_ = lean_apply_7(v_x_893_, v___x_973_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, lean_box(0));
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg___boxed(lean_object* v_x_980_, lean_object* v_isExporting_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v_isExporting_boxed_989_; uint8_t v___y_29918__boxed_990_; lean_object* v_res_991_; 
v_isExporting_boxed_989_ = lean_unbox(v_isExporting_981_);
v___y_29918__boxed_990_ = lean_unbox(v___y_982_);
v_res_991_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_980_, v_isExporting_boxed_989_, v___y_29918__boxed_990_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(lean_object* v_x_992_, uint8_t v_when_993_, uint8_t v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
if (v_when_993_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_box(v___y_994_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
v___x_1002_ = lean_apply_7(v_x_992_, v___x_1001_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, lean_box(0));
return v___x_1002_;
}
else
{
uint8_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = 0;
v___x_1004_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_992_, v___x_1003_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg___boxed(lean_object* v_x_1005_, lean_object* v_when_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v_when_boxed_1014_; uint8_t v___y_30069__boxed_1015_; lean_object* v_res_1016_; 
v_when_boxed_1014_ = lean_unbox(v_when_1006_);
v___y_30069__boxed_1015_ = lean_unbox(v___y_1007_);
v_res_1016_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v_x_1005_, v_when_boxed_1014_, v___y_30069__boxed_1015_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(lean_object* v_proof_1017_, uint8_t v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
lean_inc(v___y_1023_);
lean_inc_ref(v___y_1022_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
v___x_1025_ = lean_infer_type(v_proof_1017_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed(lean_object* v_proof_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___y_30098__boxed_1034_; lean_object* v_res_1035_; 
v___y_30098__boxed_1034_ = lean_unbox(v___y_1027_);
v_res_1035_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0(v_proof_1026_, v___y_30098__boxed_1034_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(lean_object* v_proof_1036_, uint8_t v_cache_1037_, lean_object* v_postprocessType_1038_, uint8_t v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___f_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; 
lean_inc_ref(v_proof_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1046_, 0, v_proof_1036_);
v___x_1047_ = 1;
v___x_1048_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v___f_1046_, v___x_1047_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_Core_betaReduce(v_a_1049_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = l_Lean_Meta_zetaReduce(v_a_1051_, v___x_1047_, v___x_1047_, v___x_1047_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = lean_box(v___y_1039_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
v___x_1055_ = lean_apply_8(v_postprocessType_1038_, v_a_1053_, v___x_1054_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; uint8_t v___y_1058_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
if (v_cache_1037_ == 0)
{
v___y_1058_ = v_cache_1037_;
goto v___jp_1057_;
}
else
{
uint8_t v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_Expr_hasSorry(v_proof_1036_);
v___x_1062_ = lean_bool_not(v___x_1061_);
v___y_1058_ = v___x_1062_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_Lean_Meta_mkAuxTheorem(v_a_1056_, v_proof_1036_, v___x_1047_, v___x_1059_, v___y_1058_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1060_;
}
}
else
{
lean_dec_ref(v_proof_1036_);
return v___x_1055_;
}
}
else
{
lean_dec_ref(v_postprocessType_1038_);
lean_dec_ref(v_proof_1036_);
return v___x_1052_;
}
}
else
{
lean_dec_ref(v_postprocessType_1038_);
lean_dec_ref(v_proof_1036_);
return v___x_1050_;
}
}
else
{
lean_dec_ref(v_postprocessType_1038_);
lean_dec_ref(v_proof_1036_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9___boxed(lean_object* v_proof_1063_, lean_object* v_cache_1064_, lean_object* v_postprocessType_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v_cache_boxed_1073_; uint8_t v___y_30121__boxed_1074_; lean_object* v_res_1075_; 
v_cache_boxed_1073_ = lean_unbox(v_cache_1064_);
v___y_30121__boxed_1074_ = lean_unbox(v___y_1066_);
v_res_1075_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_proof_1063_, v_cache_boxed_1073_, v_postprocessType_1065_, v___y_30121__boxed_1074_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
return v_x_1076_;
}
else
{
lean_object* v_key_1078_; lean_object* v_value_1079_; lean_object* v_tail_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1103_; 
v_key_1078_ = lean_ctor_get(v_x_1077_, 0);
v_value_1079_ = lean_ctor_get(v_x_1077_, 1);
v_tail_1080_ = lean_ctor_get(v_x_1077_, 2);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1082_ = v_x_1077_;
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_tail_1080_);
lean_inc(v_value_1079_);
lean_inc(v_key_1078_);
lean_dec(v_x_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1103_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v_fold_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1084_ = lean_array_get_size(v_x_1076_);
v___x_1085_ = l_Lean_ExprStructEq_hash(v_key_1078_);
v___x_1086_ = 32ULL;
v___x_1087_ = lean_uint64_shift_right(v___x_1085_, v___x_1086_);
v_fold_1088_ = lean_uint64_xor(v___x_1085_, v___x_1087_);
v___x_1089_ = 16ULL;
v___x_1090_ = lean_uint64_shift_right(v_fold_1088_, v___x_1089_);
v___x_1091_ = lean_uint64_xor(v_fold_1088_, v___x_1090_);
v___x_1092_ = lean_uint64_to_usize(v___x_1091_);
v___x_1093_ = lean_usize_of_nat(v___x_1084_);
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_sub(v___x_1093_, v___x_1094_);
v___x_1096_ = lean_usize_land(v___x_1092_, v___x_1095_);
v___x_1097_ = lean_array_uget_borrowed(v_x_1076_, v___x_1096_);
lean_inc(v___x_1097_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 2, v___x_1097_);
v___x_1099_ = v___x_1082_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_key_1078_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_value_1079_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_array_uset(v_x_1076_, v___x_1096_, v___x_1099_);
v_x_1076_ = v___x_1100_;
v_x_1077_ = v_tail_1080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(lean_object* v_i_1104_, lean_object* v_source_1105_, lean_object* v_target_1106_){
_start:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_array_get_size(v_source_1105_);
v___x_1108_ = lean_nat_dec_lt(v_i_1104_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v_source_1105_);
lean_dec(v_i_1104_);
return v_target_1106_;
}
else
{
lean_object* v_es_1109_; lean_object* v___x_1110_; lean_object* v_source_1111_; lean_object* v_target_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_es_1109_ = lean_array_fget(v_source_1105_, v_i_1104_);
v___x_1110_ = lean_box(0);
v_source_1111_ = lean_array_fset(v_source_1105_, v_i_1104_, v___x_1110_);
v_target_1112_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_target_1106_, v_es_1109_);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_i_1104_, v___x_1113_);
lean_dec(v_i_1104_);
v_i_1104_ = v___x_1114_;
v_source_1105_ = v_source_1111_;
v_target_1106_ = v_target_1112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(lean_object* v_data_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_nbuckets_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1117_ = lean_array_get_size(v_data_1116_);
v___x_1118_ = lean_unsigned_to_nat(2u);
v_nbuckets_1119_ = lean_nat_mul(v___x_1117_, v___x_1118_);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_mk_array(v_nbuckets_1119_, v___x_1121_);
v___x_1123_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v___x_1120_, v_data_1116_, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(lean_object* v_a_1124_, lean_object* v_x_1125_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 0)
{
uint8_t v___x_1126_; 
v___x_1126_ = 0;
return v___x_1126_;
}
else
{
lean_object* v_key_1127_; lean_object* v_tail_1128_; uint8_t v___x_1129_; 
v_key_1127_ = lean_ctor_get(v_x_1125_, 0);
v_tail_1128_ = lean_ctor_get(v_x_1125_, 2);
v___x_1129_ = l_Lean_ExprStructEq_beq(v_key_1127_, v_a_1124_);
if (v___x_1129_ == 0)
{
v_x_1125_ = v_tail_1128_;
goto _start;
}
else
{
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_1131_, lean_object* v_x_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1131_, v_x_1132_);
lean_dec(v_x_1132_);
lean_dec_ref(v_a_1131_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
lean_dec(v_b_1136_);
lean_dec_ref(v_a_1135_);
return v_x_1137_;
}
else
{
lean_object* v_key_1138_; lean_object* v_value_1139_; lean_object* v_tail_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1152_; 
v_key_1138_ = lean_ctor_get(v_x_1137_, 0);
v_value_1139_ = lean_ctor_get(v_x_1137_, 1);
v_tail_1140_ = lean_ctor_get(v_x_1137_, 2);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_x_1137_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1142_ = v_x_1137_;
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_tail_1140_);
lean_inc(v_value_1139_);
lean_inc(v_key_1138_);
lean_dec(v_x_1137_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_Lean_ExprStructEq_beq(v_key_1138_, v_a_1135_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1135_, v_b_1136_, v_tail_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 2, v___x_1145_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_key_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_value_1139_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v___x_1150_; 
lean_dec(v_value_1139_);
lean_dec(v_key_1138_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_b_1136_);
lean_ctor_set(v___x_1142_, 0, v_a_1135_);
v___x_1150_ = v___x_1142_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_b_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_tail_1140_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(lean_object* v_m_1153_, lean_object* v_a_1154_, lean_object* v_b_1155_){
_start:
{
lean_object* v_size_1156_; lean_object* v_buckets_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1200_; 
v_size_1156_ = lean_ctor_get(v_m_1153_, 0);
v_buckets_1157_ = lean_ctor_get(v_m_1153_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_m_1153_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1159_ = v_m_1153_;
v_isShared_1160_ = v_isSharedCheck_1200_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_buckets_1157_);
lean_inc(v_size_1156_);
lean_dec(v_m_1153_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1200_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; uint64_t v___x_1164_; uint64_t v_fold_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; lean_object* v_bkt_1174_; uint8_t v___x_1175_; 
v___x_1161_ = lean_array_get_size(v_buckets_1157_);
v___x_1162_ = l_Lean_ExprStructEq_hash(v_a_1154_);
v___x_1163_ = 32ULL;
v___x_1164_ = lean_uint64_shift_right(v___x_1162_, v___x_1163_);
v_fold_1165_ = lean_uint64_xor(v___x_1162_, v___x_1164_);
v___x_1166_ = 16ULL;
v___x_1167_ = lean_uint64_shift_right(v_fold_1165_, v___x_1166_);
v___x_1168_ = lean_uint64_xor(v_fold_1165_, v___x_1167_);
v___x_1169_ = lean_uint64_to_usize(v___x_1168_);
v___x_1170_ = lean_usize_of_nat(v___x_1161_);
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_sub(v___x_1170_, v___x_1171_);
v___x_1173_ = lean_usize_land(v___x_1169_, v___x_1172_);
v_bkt_1174_ = lean_array_uget_borrowed(v_buckets_1157_, v___x_1173_);
v___x_1175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1154_, v_bkt_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v_size_x27_1177_; lean_object* v___x_1178_; lean_object* v_buckets_x27_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
v_size_x27_1177_ = lean_nat_add(v_size_1156_, v___x_1176_);
lean_dec(v_size_1156_);
lean_inc(v_bkt_1174_);
v___x_1178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1178_, 0, v_a_1154_);
lean_ctor_set(v___x_1178_, 1, v_b_1155_);
lean_ctor_set(v___x_1178_, 2, v_bkt_1174_);
v_buckets_x27_1179_ = lean_array_uset(v_buckets_1157_, v___x_1173_, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(4u);
v___x_1181_ = lean_nat_mul(v_size_x27_1177_, v___x_1180_);
v___x_1182_ = lean_unsigned_to_nat(3u);
v___x_1183_ = lean_nat_div(v___x_1181_, v___x_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_array_get_size(v_buckets_x27_1179_);
v___x_1185_ = lean_nat_dec_le(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
if (v___x_1185_ == 0)
{
lean_object* v_val_1186_; lean_object* v___x_1188_; 
v_val_1186_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_buckets_x27_1179_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_val_1186_);
lean_ctor_set(v___x_1159_, 0, v_size_x27_1177_);
v___x_1188_ = v___x_1159_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_size_x27_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_val_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
else
{
lean_object* v___x_1191_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_buckets_x27_1179_);
lean_ctor_set(v___x_1159_, 0, v_size_x27_1177_);
v___x_1191_ = v___x_1159_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_size_x27_1177_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_buckets_x27_1179_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v_buckets_x27_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc(v_bkt_1174_);
v___x_1193_ = lean_box(0);
v_buckets_x27_1194_ = lean_array_uset(v_buckets_1157_, v___x_1173_, v___x_1193_);
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1154_, v_b_1155_, v_bkt_1174_);
v___x_1196_ = lean_array_uset(v_buckets_x27_1194_, v___x_1173_, v___x_1195_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1196_);
v___x_1198_ = v___x_1159_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_1156_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(lean_object* v_as_1202_, size_t v_sz_1203_, size_t v_i_1204_, lean_object* v_b_1205_, uint8_t v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_a_1214_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; uint8_t v___x_1227_; 
v___x_1227_ = lean_usize_dec_lt(v_i_1204_, v_sz_1203_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_b_1205_);
return v___x_1228_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v_localDecl_1232_; lean_object* v___x_1240_; 
v_a_1229_ = lean_array_uget_borrowed(v_as_1202_, v_i_1204_);
v___x_1230_ = l_Lean_Expr_fvarId_x21(v_a_1229_);
lean_inc(v___x_1230_);
v___x_1240_ = l_Lean_FVarId_getDecl___redArg(v___x_1230_, v___y_1208_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1242_ = l_Lean_LocalDecl_type(v_a_1241_);
v___x_1243_ = l_Lean_Meta_AbstractNestedProofs_visit(v___x_1242_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = l_Lean_LocalDecl_setType(v_a_1241_, v_a_1244_);
v___x_1246_ = l_Lean_LocalDecl_value_x3f(v___x_1245_, v___x_1227_);
if (lean_obj_tag(v___x_1246_) == 0)
{
v_localDecl_1232_ = v___x_1245_;
goto v___jp_1231_;
}
else
{
lean_object* v_val_1247_; lean_object* v___x_1248_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = l_Lean_Meta_AbstractNestedProofs_visit(v_val_1247_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = l_Lean_LocalDecl_setValue(v___x_1245_, v_a_1249_);
v_localDecl_1232_ = v___x_1250_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v___x_1245_);
lean_dec(v___x_1230_);
lean_dec_ref(v_b_1205_);
v_a_1251_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1248_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1248_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1241_);
lean_dec(v___x_1230_);
lean_dec_ref(v_b_1205_);
v_a_1259_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1243_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1243_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v___x_1230_);
lean_dec_ref(v_b_1205_);
v_a_1267_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1240_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1240_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
v___jp_1231_:
{
lean_object* v_fvarIdToDecl_1233_; lean_object* v_decls_1234_; lean_object* v_auxDeclToFullName_1235_; lean_object* v___x_1236_; 
v_fvarIdToDecl_1233_ = lean_ctor_get(v_b_1205_, 0);
v_decls_1234_ = lean_ctor_get(v_b_1205_, 1);
v_auxDeclToFullName_1235_ = lean_ctor_get(v_b_1205_, 2);
lean_inc_ref(v_b_1205_);
v___x_1236_ = lean_local_ctx_find(v_b_1205_, v___x_1230_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_dec_ref(v_localDecl_1232_);
v_a_1214_ = v_b_1205_;
goto v___jp_1213_;
}
else
{
lean_object* v_index_1237_; lean_object* v_fvarId_1238_; lean_object* v___x_1239_; 
lean_inc(v_auxDeclToFullName_1235_);
lean_inc_ref(v_decls_1234_);
lean_inc_ref(v_fvarIdToDecl_1233_);
lean_dec_ref_known(v___x_1236_, 1);
lean_dec_ref(v_b_1205_);
v_index_1237_ = lean_ctor_get(v_localDecl_1232_, 0);
lean_inc(v_index_1237_);
v_fvarId_1238_ = lean_ctor_get(v_localDecl_1232_, 1);
lean_inc_ref(v_localDecl_1232_);
lean_inc(v_fvarId_1238_);
v___x_1239_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_fvarIdToDecl_1233_, v_fvarId_1238_, v_localDecl_1232_);
v___y_1219_ = v_localDecl_1232_;
v___y_1220_ = v___x_1239_;
v___y_1221_ = v_decls_1234_;
v___y_1222_ = v_auxDeclToFullName_1235_;
v___y_1223_ = v_index_1237_;
goto v___jp_1218_;
}
}
}
v___jp_1213_:
{
size_t v___x_1215_; size_t v___x_1216_; 
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1204_, v___x_1215_);
v_i_1204_ = v___x_1216_;
v_b_1205_ = v_a_1214_;
goto _start;
}
v___jp_1218_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1219_);
v___x_1225_ = l_Lean_PersistentArray_set___redArg(v___y_1221_, v___y_1223_, v___x_1224_);
lean_dec(v___y_1223_);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1220_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_ctor_set(v___x_1226_, 2, v___y_1222_);
v_a_1214_ = v___x_1226_;
goto v___jp_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0(lean_object* v_xs_1275_, lean_object* v_k_1276_, uint8_t v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_lctx_1284_; lean_object* v_localInstances_1285_; size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_lctx_1284_ = lean_ctor_get(v___y_1279_, 2);
v_localInstances_1285_ = lean_ctor_get(v___y_1279_, 3);
v_sz_1286_ = lean_array_size(v_xs_1275_);
v___x_1287_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1284_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(v_xs_1275_, v_sz_1286_, v___x_1287_, v_lctx_1284_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
lean_inc_ref(v_localInstances_1285_);
v___x_1290_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_AbstractNestedProofs_visit_spec__5___redArg(v_a_1289_, v_localInstances_1285_, v_k_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1290_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_k_1276_);
v_a_1291_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1288_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1288_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed(lean_object* v_xs_1299_, lean_object* v_k_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v___y_30436__boxed_1308_; lean_object* v_res_1309_; 
v___y_30436__boxed_1308_ = lean_unbox(v___y_1301_);
v_res_1309_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__0(v_xs_1299_, v_k_1300_, v___y_30436__boxed_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v_xs_1299_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed(lean_object* v___y_1310_, lean_object* v___f_1311_, lean_object* v_xs_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___y_30386__boxed_1321_; uint8_t v___y_30388__boxed_1322_; lean_object* v_res_1323_; 
v___y_30386__boxed_1321_ = lean_unbox(v___y_1310_);
v___y_30388__boxed_1322_ = lean_unbox(v___y_1314_);
v_res_1323_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__2(v___y_30386__boxed_1321_, v___f_1311_, v_xs_1312_, v_b_1313_, v___y_30388__boxed_1322_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5(lean_object* v_b_1324_, lean_object* v_xs_1325_, uint8_t v___y_1326_, uint8_t v___x_1327_, uint8_t v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1324_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = 1;
v___x_1338_ = l_Lean_Meta_mkForallFVars(v_xs_1325_, v_a_1336_, v___y_1326_, v___x_1327_, v___x_1327_, v___x_1337_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1338_;
}
else
{
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed(lean_object* v_b_1339_, lean_object* v_xs_1340_, lean_object* v___y_1341_, lean_object* v___x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v___y_30422__boxed_1350_; uint8_t v___x_30423__boxed_1351_; uint8_t v___y_30424__boxed_1352_; lean_object* v_res_1353_; 
v___y_30422__boxed_1350_ = lean_unbox(v___y_1341_);
v___x_30423__boxed_1351_ = lean_unbox(v___x_1342_);
v___y_30424__boxed_1352_ = lean_unbox(v___y_1343_);
v_res_1353_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__5(v_b_1339_, v_xs_1340_, v___y_30422__boxed_1350_, v___x_30423__boxed_1351_, v___y_30424__boxed_1352_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v_xs_1340_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3(uint8_t v___y_1354_, uint8_t v___x_1355_, lean_object* v___f_1356_, lean_object* v_xs_1357_, lean_object* v_b_1358_, uint8_t v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1366_ = lean_box(v___y_1354_);
v___x_1367_ = lean_box(v___x_1355_);
lean_inc_ref(v_xs_1357_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1368_, 0, v_b_1358_);
lean_closure_set(v___f_1368_, 1, v_xs_1357_);
lean_closure_set(v___f_1368_, 2, v___x_1366_);
lean_closure_set(v___f_1368_, 3, v___x_1367_);
v___x_1369_ = lean_box(v___y_1359_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
v___x_1370_ = lean_apply_9(v___f_1356_, v_xs_1357_, v___f_1368_, v___x_1369_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, lean_box(0));
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed(lean_object* v___y_1371_, lean_object* v___x_1372_, lean_object* v___f_1373_, lean_object* v_xs_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v___y_30397__boxed_1383_; uint8_t v___x_30398__boxed_1384_; uint8_t v___y_30400__boxed_1385_; lean_object* v_res_1386_; 
v___y_30397__boxed_1383_ = lean_unbox(v___y_1371_);
v___x_30398__boxed_1384_ = lean_unbox(v___x_1372_);
v___y_30400__boxed_1385_ = lean_unbox(v___y_1376_);
v_res_1386_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__3(v___y_30397__boxed_1383_, v___x_30398__boxed_1384_, v___f_1373_, v_xs_1374_, v_b_1375_, v___y_30400__boxed_1385_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(size_t v_sz_1387_, size_t v_i_1388_, lean_object* v_bs_1389_, uint8_t v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_usize_dec_lt(v_i_1388_, v_sz_1387_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_bs_1389_);
return v___x_1398_;
}
else
{
lean_object* v_v_1399_; lean_object* v___x_1400_; 
v_v_1399_ = lean_array_uget_borrowed(v_bs_1389_, v_i_1388_);
lean_inc(v_v_1399_);
v___x_1400_ = l_Lean_Meta_AbstractNestedProofs_visit(v_v_1399_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v_bs_x27_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = lean_unsigned_to_nat(0u);
v_bs_x27_1403_ = lean_array_uset(v_bs_1389_, v_i_1388_, v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_add(v_i_1388_, v___x_1404_);
v___x_1406_ = lean_array_uset(v_bs_x27_1403_, v_i_1388_, v_a_1401_);
v_i_1388_ = v___x_1405_;
v_bs_1389_ = v___x_1406_;
goto _start;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_bs_1389_);
v_a_1408_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1400_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1400_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, uint8_t v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
if (lean_obj_tag(v_x_1416_) == 5)
{
lean_object* v_fn_1426_; lean_object* v_arg_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_fn_1426_ = lean_ctor_get(v_x_1416_, 0);
lean_inc_ref(v_fn_1426_);
v_arg_1427_ = lean_ctor_get(v_x_1416_, 1);
lean_inc_ref(v_arg_1427_);
lean_dec_ref_known(v_x_1416_, 2);
v___x_1428_ = lean_array_set(v_x_1417_, v_x_1418_, v_arg_1427_);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_nat_sub(v_x_1418_, v___x_1429_);
lean_dec(v_x_1418_);
v_x_1416_ = v_fn_1426_;
v_x_1417_ = v___x_1428_;
v_x_1418_ = v___x_1430_;
goto _start;
}
else
{
lean_object* v___x_1432_; 
lean_dec(v_x_1418_);
v___x_1432_ = l_Lean_Meta_AbstractNestedProofs_visit(v_x_1416_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; size_t v_sz_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v_sz_1434_ = lean_array_size(v_x_1417_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_1434_, v___x_1435_, v_x_1417_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1445_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1445_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = l_Lean_mkAppN(v_a_1433_, v_a_1437_);
lean_dec(v_a_1437_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1433_);
v_a_1446_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1436_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1436_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_dec_ref(v_x_1417_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___boxed(lean_object* v_e_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
uint8_t v_a_boxed_1462_; lean_object* v_res_1463_; 
v_a_boxed_1462_ = lean_unbox(v_a_1455_);
v_res_1463_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1454_, v_a_boxed_1462_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* v_e_1464_, uint8_t v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_a_1473_; lean_object* v___y_1479_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Lean_Meta_AbstractNestedProofs_visit___closed__0));
v___x_1482_ = l_Lean_Core_checkSystem(v___x_1481_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1549_; 
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1482_, 0);
lean_dec(v_unused_1550_);
v___x_1484_ = v___x_1482_;
v_isShared_1485_ = v_isSharedCheck_1549_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v___x_1482_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1549_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Lean_Expr_isAtomic(v_e_1464_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_st_ref_get(v_a_1466_);
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v___x_1487_, v_e_1464_);
lean_dec(v___x_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; 
lean_del_object(v___x_1484_);
lean_inc_ref(v_e_1464_);
v___x_1489_ = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(v_e_1464_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___f_1491_; uint8_t v___x_1492_; uint8_t v___y_1494_; uint8_t v___x_1528_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__0___boxed), 9, 0);
v___x_1492_ = 1;
v___x_1528_ = lean_unbox(v_a_1490_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_unbox(v_a_1490_);
lean_dec(v_a_1490_);
v___y_1494_ = v___x_1529_;
goto v___jp_1493_;
}
else
{
uint8_t v___x_1530_; uint8_t v___x_1531_; 
lean_dec(v_a_1490_);
v___x_1530_ = l_Lean_Expr_hasSorry(v_e_1464_);
v___x_1531_ = lean_bool_not(v___x_1530_);
if (v___x_1531_ == 0)
{
v___y_1494_ = v___x_1531_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec_ref(v___f_1491_);
v___x_1532_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___boxed), 8, 0);
lean_inc_ref(v_e_1464_);
v___x_1533_ = l_Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9(v_e_1464_, v_a_1465_, v___x_1532_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
v___y_1479_ = v___x_1533_;
goto v___jp_1478_;
}
}
v___jp_1493_:
{
switch(lean_obj_tag(v_e_1464_))
{
case 6:
{
lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_box(v___y_1494_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1496_, 0, v___x_1495_);
lean_closure_set(v___f_1496_, 1, v___f_1491_);
lean_inc_ref(v_e_1464_);
v___x_1497_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_1464_, v___f_1496_, v___y_1494_, v___x_1492_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
v___y_1479_ = v___x_1497_;
goto v___jp_1478_;
}
case 8:
{
lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_box(v___y_1494_);
v___f_1499_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__2___boxed), 11, 2);
lean_closure_set(v___f_1499_, 0, v___x_1498_);
lean_closure_set(v___f_1499_, 1, v___f_1491_);
lean_inc_ref(v_e_1464_);
v___x_1500_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__6___redArg(v_e_1464_, v___f_1499_, v___y_1494_, v___x_1492_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
v___y_1479_ = v___x_1500_;
goto v___jp_1478_;
}
case 7:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_box(v___y_1494_);
v___x_1502_ = lean_box(v___x_1492_);
v___f_1503_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__3___boxed), 12, 3);
lean_closure_set(v___f_1503_, 0, v___x_1501_);
lean_closure_set(v___f_1503_, 1, v___x_1502_);
lean_closure_set(v___f_1503_, 2, v___f_1491_);
lean_inc_ref(v_e_1464_);
v___x_1504_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_AbstractNestedProofs_visit_spec__7___redArg(v_e_1464_, v___f_1503_, v___y_1494_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
v___y_1479_ = v___x_1504_;
goto v___jp_1478_;
}
case 10:
{
lean_object* v_data_1505_; lean_object* v_expr_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v___f_1491_);
v_data_1505_ = lean_ctor_get(v_e_1464_, 0);
v_expr_1506_ = lean_ctor_get(v_e_1464_, 1);
lean_inc_ref(v_expr_1506_);
v___x_1507_ = l_Lean_Meta_AbstractNestedProofs_visit(v_expr_1506_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1509_ = lean_ptr_addr(v_expr_1506_);
v___x_1510_ = lean_ptr_addr(v_a_1508_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_inc(v_data_1505_);
v___x_1512_ = l_Lean_Expr_mdata___override(v_data_1505_, v_a_1508_);
v_a_1473_ = v___x_1512_;
goto v___jp_1472_;
}
else
{
lean_dec(v_a_1508_);
lean_inc_ref(v_e_1464_);
v_a_1473_ = v_e_1464_;
goto v___jp_1472_;
}
}
else
{
v___y_1479_ = v___x_1507_;
goto v___jp_1478_;
}
}
case 11:
{
lean_object* v_typeName_1513_; lean_object* v_idx_1514_; lean_object* v_struct_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v___f_1491_);
v_typeName_1513_ = lean_ctor_get(v_e_1464_, 0);
v_idx_1514_ = lean_ctor_get(v_e_1464_, 1);
v_struct_1515_ = lean_ctor_get(v_e_1464_, 2);
lean_inc_ref(v_struct_1515_);
v___x_1516_ = l_Lean_Meta_AbstractNestedProofs_visit(v_struct_1515_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_ptr_addr(v_struct_1515_);
v___x_1519_ = lean_ptr_addr(v_a_1517_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
lean_inc(v_idx_1514_);
lean_inc(v_typeName_1513_);
v___x_1521_ = l_Lean_Expr_proj___override(v_typeName_1513_, v_idx_1514_, v_a_1517_);
v_a_1473_ = v___x_1521_;
goto v___jp_1472_;
}
else
{
lean_dec(v_a_1517_);
lean_inc_ref(v_e_1464_);
v_a_1473_ = v_e_1464_;
goto v___jp_1472_;
}
}
else
{
v___y_1479_ = v___x_1516_;
goto v___jp_1478_;
}
}
case 5:
{
lean_object* v_dummy_1522_; lean_object* v_nargs_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref(v___f_1491_);
v_dummy_1522_ = lean_obj_once(&l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4, &l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4_once, _init_l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___lam__0___closed__4);
v_nargs_1523_ = l_Lean_Expr_getAppNumArgs(v_e_1464_);
lean_inc(v_nargs_1523_);
v___x_1524_ = lean_mk_array(v_nargs_1523_, v_dummy_1522_);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_sub(v_nargs_1523_, v___x_1525_);
lean_dec(v_nargs_1523_);
lean_inc_ref(v_e_1464_);
v___x_1527_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_e_1464_, v___x_1524_, v___x_1526_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
v___y_1479_ = v___x_1527_;
goto v___jp_1478_;
}
default: 
{
lean_dec_ref(v___f_1491_);
lean_inc_ref(v_e_1464_);
v_a_1473_ = v_e_1464_;
goto v___jp_1472_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_e_1464_);
v_a_1534_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1489_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1489_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v_val_1542_; lean_object* v___x_1544_; 
lean_dec_ref(v_e_1464_);
v_val_1542_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v___x_1488_, 1);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v_val_1542_);
v___x_1544_ = v___x_1484_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_val_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v___x_1547_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v_e_1464_);
v___x_1547_ = v___x_1484_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_e_1464_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v_e_1464_);
v_a_1551_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1482_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1482_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
v___jp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_st_ref_take(v_a_1466_);
lean_inc_ref(v_a_1473_);
v___x_1475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v___x_1474_, v_e_1464_, v_a_1473_);
v___x_1476_ = lean_st_ref_set(v_a_1466_, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1473_);
return v___x_1477_;
}
v___jp_1478_:
{
if (lean_obj_tag(v___y_1479_) == 0)
{
lean_object* v_a_1480_; 
v_a_1480_ = lean_ctor_get(v___y_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___y_1479_, 1);
v_a_1473_ = v_a_1480_;
goto v___jp_1472_;
}
else
{
lean_dec_ref(v_e_1464_);
return v___y_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1(lean_object* v_b_1559_, lean_object* v_xs_1560_, uint8_t v___y_1561_, uint8_t v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Meta_AbstractNestedProofs_visit(v_b_1559_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = 1;
v___x_1572_ = l_Lean_Meta_mkLambdaFVars(v_xs_1560_, v_a_1570_, v___y_1561_, v___y_1561_, v___y_1561_, v___y_1561_, v___x_1571_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
return v___x_1572_;
}
else
{
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed(lean_object* v_b_1573_, lean_object* v_xs_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v___y_30409__boxed_1583_; uint8_t v___y_30410__boxed_1584_; lean_object* v_res_1585_; 
v___y_30409__boxed_1583_ = lean_unbox(v___y_1575_);
v___y_30410__boxed_1584_ = lean_unbox(v___y_1576_);
v_res_1585_ = l_Lean_Meta_AbstractNestedProofs_visit___lam__1(v_b_1573_, v_xs_1574_, v___y_30409__boxed_1583_, v___y_30410__boxed_1584_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v_xs_1574_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractNestedProofs_visit___lam__2(uint8_t v___y_1586_, lean_object* v___f_1587_, lean_object* v_xs_1588_, lean_object* v_b_1589_, uint8_t v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1597_ = lean_box(v___y_1586_);
lean_inc_ref(v_xs_1588_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1598_, 0, v_b_1589_);
lean_closure_set(v___f_1598_, 1, v_xs_1588_);
lean_closure_set(v___f_1598_, 2, v___x_1597_);
v___x_1599_ = lean_box(v___y_1590_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1594_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
v___x_1600_ = lean_apply_9(v___f_1587_, v_xs_1588_, v___f_1598_, v___x_1599_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, lean_box(0));
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0___boxed(lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_bs_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_sz_boxed_1611_; size_t v_i_boxed_1612_; uint8_t v___y_30449__boxed_1613_; lean_object* v_res_1614_; 
v_sz_boxed_1611_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1612_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v___y_30449__boxed_1613_ = lean_unbox(v___y_1604_);
v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AbstractNestedProofs_visit_spec__0(v_sz_boxed_1611_, v_i_boxed_1612_, v_bs_1603_, v___y_30449__boxed_1613_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8___boxed(lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
uint8_t v___y_30470__boxed_1625_; lean_object* v_res_1626_; 
v___y_30470__boxed_1625_ = lean_unbox(v___y_1618_);
v_res_1626_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_AbstractNestedProofs_visit_spec__8(v_x_1615_, v_x_1616_, v_x_1617_, v___y_30470__boxed_1625_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4___boxed(lean_object* v_as_1627_, lean_object* v_sz_1628_, lean_object* v_i_1629_, lean_object* v_b_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; uint8_t v___y_30493__boxed_1640_; lean_object* v_res_1641_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1628_);
lean_dec(v_sz_1628_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v___y_30493__boxed_1640_ = lean_unbox(v___y_1631_);
v_res_1641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_AbstractNestedProofs_visit_spec__4(v_as_1627_, v_sz_boxed_1638_, v_i_boxed_1639_, v_b_1630_, v___y_30493__boxed_1640_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v_as_1627_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1(lean_object* v_00_u03b2_1642_, lean_object* v_m_1643_, lean_object* v_a_1644_, lean_object* v_b_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1___redArg(v_m_1643_, v_a_1644_, v_b_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(lean_object* v_00_u03b2_1647_, lean_object* v_m_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___redArg(v_m_1648_, v_a_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_m_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2(v_00_u03b2_1651_, v_m_1652_, v_a_1653_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_m_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3(lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3___redArg(v_x_1656_, v_x_1657_, v_x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(lean_object* v_00_u03b2_1660_, lean_object* v_a_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___redArg(v_a_1661_, v_x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_a_1665_, lean_object* v_x_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__1(v_00_u03b2_1664_, v_a_1665_, v_x_1666_);
lean_dec(v_x_1666_);
lean_dec_ref(v_a_1665_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2(lean_object* v_00_u03b2_1669_, lean_object* v_data_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2___redArg(v_data_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3(lean_object* v_00_u03b2_1672_, lean_object* v_a_1673_, lean_object* v_b_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__3___redArg(v_a_1673_, v_b_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(lean_object* v_00_u03b2_1677_, lean_object* v_a_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___redArg(v_a_1678_, v_x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_a_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractNestedProofs_visit_spec__2_spec__5(v_00_u03b2_1681_, v_a_1682_, v_x_1683_);
lean_dec(v_x_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, size_t v_x_1687_, size_t v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___redArg(v_x_1686_, v_x_1687_, v_x_1688_, v_x_1689_, v_x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_, lean_object* v_x_1697_){
_start:
{
size_t v_x_31091__boxed_1698_; size_t v_x_31092__boxed_1699_; lean_object* v_res_1700_; 
v_x_31091__boxed_1698_ = lean_unbox_usize(v_x_1694_);
lean_dec(v_x_1694_);
v_x_31092__boxed_1699_ = lean_unbox_usize(v_x_1695_);
lean_dec(v_x_1695_);
v_res_1700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7(v_00_u03b2_1692_, v_x_1693_, v_x_31091__boxed_1698_, v_x_31092__boxed_1699_, v_x_1696_, v_x_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(lean_object* v_00_u03b1_1701_, lean_object* v_x_1702_, uint8_t v_isExporting_1703_, uint8_t v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___redArg(v_x_1702_, v_isExporting_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_x_1713_, lean_object* v_isExporting_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_isExporting_boxed_1722_; uint8_t v___y_31107__boxed_1723_; lean_object* v_res_1724_; 
v_isExporting_boxed_1722_ = lean_unbox(v_isExporting_1714_);
v___y_31107__boxed_1723_ = lean_unbox(v___y_1715_);
v_res_1724_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14_spec__18(v_00_u03b1_1712_, v_x_1713_, v_isExporting_boxed_1722_, v___y_31107__boxed_1723_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(lean_object* v_00_u03b1_1725_, lean_object* v_x_1726_, uint8_t v_when_1727_, uint8_t v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___redArg(v_x_1726_, v_when_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_x_1737_, lean_object* v_when_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v_when_boxed_1746_; uint8_t v___y_31130__boxed_1747_; lean_object* v_res_1748_; 
v_when_boxed_1746_ = lean_unbox(v_when_1738_);
v___y_31130__boxed_1747_ = lean_unbox(v___y_1739_);
v_res_1748_ = l_Lean_withoutExporting___at___00Lean_Meta_abstractProof___at___00Lean_Meta_AbstractNestedProofs_visit_spec__9_spec__14(v_00_u03b1_1736_, v_x_1737_, v_when_boxed_1746_, v___y_31130__boxed_1747_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1749_, lean_object* v_i_1750_, lean_object* v_source_1751_, lean_object* v_target_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6___redArg(v_i_1750_, v_source_1751_, v_target_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12(lean_object* v_00_u03b2_1754_, lean_object* v_n_1755_, lean_object* v_k_1756_, lean_object* v_v_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12___redArg(v_n_1755_, v_k_1756_, v_v_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_1759_, size_t v_depth_1760_, lean_object* v_keys_1761_, lean_object* v_vals_1762_, lean_object* v_heq_1763_, lean_object* v_i_1764_, lean_object* v_entries_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___redArg(v_depth_1760_, v_keys_1761_, v_vals_1762_, v_i_1764_, v_entries_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13___boxed(lean_object* v_00_u03b2_1767_, lean_object* v_depth_1768_, lean_object* v_keys_1769_, lean_object* v_vals_1770_, lean_object* v_heq_1771_, lean_object* v_i_1772_, lean_object* v_entries_1773_){
_start:
{
size_t v_depth_boxed_1774_; lean_object* v_res_1775_; 
v_depth_boxed_1774_ = lean_unbox_usize(v_depth_1768_);
lean_dec(v_depth_1768_);
v_res_1775_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__13(v_00_u03b2_1767_, v_depth_boxed_1774_, v_keys_1769_, v_vals_1770_, v_heq_1771_, v_i_1772_, v_entries_1773_);
lean_dec_ref(v_vals_1770_);
lean_dec_ref(v_keys_1769_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12(lean_object* v_00_u03b2_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__1_spec__2_spec__6_spec__12___redArg(v_x_1777_, v_x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_AbstractNestedProofs_visit_spec__3_spec__7_spec__12_spec__17___redArg(v_x_1781_, v_x_1782_, v_x_1783_, v_x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__0(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_unsigned_to_nat(16u);
v___x_1788_ = lean_mk_array(v___x_1787_, v___x_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_Meta_abstractNestedProofs___closed__1(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__0, &l_Lean_Meta_abstractNestedProofs___closed__0_once, _init_l_Lean_Meta_abstractNestedProofs___closed__0);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* v_e_1792_, uint8_t v_cache_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; 
lean_inc_ref(v_e_1792_);
v___x_1799_ = l_Lean_Meta_isProof(v_e_1792_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1820_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1820_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1820_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_unbox(v_a_1800_);
lean_dec(v_a_1800_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_del_object(v___x_1802_);
v___x_1805_ = lean_obj_once(&l_Lean_Meta_abstractNestedProofs___closed__1, &l_Lean_Meta_abstractNestedProofs___closed__1_once, _init_l_Lean_Meta_abstractNestedProofs___closed__1);
v___x_1806_ = lean_st_mk_ref(v___x_1805_);
v___x_1807_ = l_Lean_Meta_AbstractNestedProofs_visit(v_e_1792_, v_cache_1793_, v___x_1806_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1816_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_st_ref_get(v___x_1806_);
lean_dec(v___x_1806_);
lean_dec(v___x_1812_);
if (v_isShared_1811_ == 0)
{
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1808_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_dec(v___x_1806_);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1818_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v_e_1792_);
v___x_1818_ = v___x_1802_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_e_1792_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec_ref(v_e_1792_);
v_a_1821_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1799_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1799_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object* v_e_1829_, lean_object* v_cache_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
uint8_t v_cache_boxed_1836_; lean_object* v_res_1837_; 
v_cache_boxed_1836_ = lean_unbox(v_cache_1830_);
v_res_1837_ = l_Lean_Meta_abstractNestedProofs(v_e_1829_, v_cache_boxed_1836_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
return v_res_1837_;
}
}
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
