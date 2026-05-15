// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Lambda
// Imports: public import Lean.Meta.Sym.Simp.SimpM
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "f'"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 166, 137, 10, 240, 99, 97, 180)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "g"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 12, 229, 162, 1, 36, 3, 29)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpLambda___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpLambda___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpLambda___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = l_Lean_Expr_bvar___override(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = l_Lean_Expr_bvar___override(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(lean_object* v___x_11_, lean_object* v_a_12_, lean_object* v___x_13_, lean_object* v_xs_14_, lean_object* v___x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_00_u03b2_20_, uint8_t v___x_21_, uint8_t v___x_22_, uint8_t v___x_23_, lean_object* v___x_24_, lean_object* v_f_25_, lean_object* v_g_26_, lean_object* v_h_27_, lean_object* v___x_28_, lean_object* v_f_x27_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_35_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__0));
lean_inc_ref(v___x_11_);
v___x_36_ = l_Lean_Name_mkStr2(v___x_11_, v___x_35_);
lean_inc(v_a_12_);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v_a_12_);
lean_ctor_set(v___x_37_, 1, v___x_13_);
v___x_38_ = l_Lean_mkConst(v___x_36_, v___x_37_);
v___x_39_ = 0;
v___x_40_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1, &l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__1);
v___x_41_ = l_Lean_mkAppN(v___x_40_, v_xs_14_);
lean_inc_ref(v___x_41_);
lean_inc_ref_n(v_a_16_, 4);
lean_inc(v___x_15_);
v___x_42_ = l_Lean_mkLambda(v___x_15_, v___x_39_, v_a_16_, v___x_41_);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2, &l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__2);
lean_inc_ref_n(v_a_17_, 2);
v___x_45_ = l_Lean_mkAppB(v_a_17_, v___x_44_, v___x_40_);
v___x_46_ = l_Lean_mkLambda(v___x_18_, v___x_39_, v___x_45_, v___x_41_);
v___x_47_ = l_Lean_mkLambda(v___x_19_, v___x_39_, v_a_16_, v___x_46_);
v___x_48_ = l_Lean_mkLambda(v___x_15_, v___x_39_, v_a_16_, v___x_47_);
lean_inc_ref(v_f_x27_29_);
v___x_49_ = l_Lean_mkApp6(v___x_38_, v_a_16_, v_a_17_, v_00_u03b2_20_, v___x_42_, v___x_48_, v_f_x27_29_);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_51_ = lean_array_push(v___x_50_, v_f_x27_29_);
v___x_52_ = l_Array_append___redArg(v___x_51_, v_xs_14_);
v___x_53_ = l_Lean_Meta_mkLambdaFVars(v___x_52_, v___x_49_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec_ref(v___x_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref(v___x_53_);
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__3));
lean_inc_ref(v___x_11_);
v___x_56_ = l_Lean_Name_mkStr2(v___x_11_, v___x_55_);
lean_inc_n(v___x_24_, 2);
v___x_57_ = l_Lean_mkConst(v___x_56_, v___x_24_);
lean_inc_ref(v_h_27_);
lean_inc_ref_n(v_g_26_, 2);
lean_inc_ref_n(v_f_25_, 2);
lean_inc_ref_n(v_a_17_, 2);
lean_inc_ref_n(v_a_16_, 3);
v___x_58_ = l_Lean_mkApp5(v___x_57_, v_a_16_, v_a_17_, v_f_25_, v_g_26_, v_h_27_);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__4));
v___x_60_ = l_Lean_Name_mkStr2(v___x_11_, v___x_59_);
v___x_61_ = l_Lean_mkConst(v___x_60_, v___x_24_);
lean_inc_ref(v___x_61_);
v___x_62_ = l_Lean_mkApp3(v___x_61_, v_a_16_, v_a_17_, v_f_25_);
v___x_63_ = l_Lean_mkApp3(v___x_61_, v_a_16_, v_a_17_, v_g_26_);
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___closed__6));
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v_a_12_);
lean_ctor_set(v___x_65_, 1, v___x_24_);
v___x_66_ = l_Lean_mkConst(v___x_64_, v___x_65_);
v___x_67_ = l_Lean_mkApp6(v___x_66_, v___x_28_, v_a_16_, v___x_62_, v___x_63_, v_a_54_, v___x_58_);
v___x_68_ = lean_unsigned_to_nat(3u);
v___x_69_ = lean_mk_empty_array_with_capacity(v___x_68_);
v___x_70_ = lean_array_push(v___x_69_, v_f_25_);
v___x_71_ = lean_array_push(v___x_70_, v_g_26_);
v___x_72_ = lean_array_push(v___x_71_, v_h_27_);
v___x_73_ = l_Lean_Meta_mkLambdaFVars(v___x_72_, v___x_67_, v___x_21_, v___x_22_, v___x_21_, v___x_22_, v___x_23_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec_ref(v___x_72_);
return v___x_73_;
}
else
{
lean_dec_ref(v___x_28_);
lean_dec_ref(v_h_27_);
lean_dec_ref(v_g_26_);
lean_dec_ref(v_f_25_);
lean_dec(v___x_24_);
lean_dec_ref(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_12_);
lean_dec_ref(v___x_11_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed(lean_object** _args){
lean_object* v___x_74_ = _args[0];
lean_object* v_a_75_ = _args[1];
lean_object* v___x_76_ = _args[2];
lean_object* v_xs_77_ = _args[3];
lean_object* v___x_78_ = _args[4];
lean_object* v_a_79_ = _args[5];
lean_object* v_a_80_ = _args[6];
lean_object* v___x_81_ = _args[7];
lean_object* v___x_82_ = _args[8];
lean_object* v_00_u03b2_83_ = _args[9];
lean_object* v___x_84_ = _args[10];
lean_object* v___x_85_ = _args[11];
lean_object* v___x_86_ = _args[12];
lean_object* v___x_87_ = _args[13];
lean_object* v_f_88_ = _args[14];
lean_object* v_g_89_ = _args[15];
lean_object* v_h_90_ = _args[16];
lean_object* v___x_91_ = _args[17];
lean_object* v_f_x27_92_ = _args[18];
lean_object* v___y_93_ = _args[19];
lean_object* v___y_94_ = _args[20];
lean_object* v___y_95_ = _args[21];
lean_object* v___y_96_ = _args[22];
lean_object* v___y_97_ = _args[23];
_start:
{
uint8_t v___x_1958__boxed_98_; uint8_t v___x_1959__boxed_99_; uint8_t v___x_1960__boxed_100_; lean_object* v_res_101_; 
v___x_1958__boxed_98_ = lean_unbox(v___x_84_);
v___x_1959__boxed_99_ = lean_unbox(v___x_85_);
v___x_1960__boxed_100_ = lean_unbox(v___x_86_);
v_res_101_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(v___x_74_, v_a_75_, v___x_76_, v_xs_77_, v___x_78_, v_a_79_, v_a_80_, v___x_81_, v___x_82_, v_00_u03b2_83_, v___x_1958__boxed_98_, v___x_1959__boxed_99_, v___x_1960__boxed_100_, v___x_87_, v_f_88_, v_g_89_, v_h_90_, v___x_91_, v_f_x27_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_xs_77_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(lean_object* v_k_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
v___x_109_ = lean_apply_6(v_k_102_, v_b_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(v_k_110_, v_b_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(lean_object* v_name_118_, uint8_t v_bi_119_, lean_object* v_type_120_, lean_object* v_k_121_, uint8_t v_kind_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_128_, 0, v_k_121_);
v___x_129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_118_, v_bi_119_, v_type_120_, v___f_128_, v_kind_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_129_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_129_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___boxed(lean_object* v_name_146_, lean_object* v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, lean_object* v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_bi_boxed_156_; uint8_t v_kind_boxed_157_; lean_object* v_res_158_; 
v_bi_boxed_156_ = lean_unbox(v_bi_147_);
v_kind_boxed_157_ = lean_unbox(v_kind_150_);
v_res_158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_146_, v_bi_boxed_156_, v_type_148_, v_k_149_, v_kind_boxed_157_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(lean_object* v_name_159_, lean_object* v_type_160_, lean_object* v_k_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = 0;
v___x_168_ = 0;
v___x_169_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_159_, v___x_167_, v_type_160_, v_k_161_, v___x_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg___boxed(lean_object* v_name_170_, lean_object* v_type_171_, lean_object* v_k_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_170_, v_type_171_, v_k_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(lean_object* v_xs_185_, lean_object* v___x_186_, uint8_t v___x_187_, uint8_t v___x_188_, uint8_t v___x_189_, lean_object* v_f_190_, lean_object* v_g_191_, lean_object* v_a_192_, lean_object* v___x_193_, lean_object* v_a_194_, lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v_00_u03b2_199_, lean_object* v_h_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_mkForallFVars(v_xs_185_, v___x_186_, v___x_187_, v___x_188_, v___x_188_, v___x_189_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = lean_mk_empty_array_with_capacity(v___x_208_);
lean_inc_ref(v_f_190_);
v___x_210_ = lean_array_push(v___x_209_, v_f_190_);
lean_inc_ref(v_g_191_);
v___x_211_ = lean_array_push(v___x_210_, v_g_191_);
v___x_212_ = l_Lean_Meta_mkLambdaFVars(v___x_211_, v_a_207_, v___x_187_, v___x_188_, v___x_187_, v___x_188_, v___x_189_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec_ref(v___x_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc_n(v_a_213_, 2);
lean_dec_ref(v___x_212_);
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0));
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1));
lean_inc(v_a_192_);
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v_a_192_);
lean_ctor_set(v___x_216_, 1, v___x_193_);
lean_inc_ref(v___x_216_);
v___x_217_ = l_Lean_mkConst(v___x_215_, v___x_216_);
lean_inc_ref(v_a_194_);
v___x_218_ = l_Lean_mkAppB(v___x_217_, v_a_194_, v_a_213_);
v___x_219_ = lean_box(v___x_187_);
v___x_220_ = lean_box(v___x_188_);
v___x_221_ = lean_box(v___x_189_);
lean_inc_ref(v___x_218_);
v___f_222_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed), 24, 18);
lean_closure_set(v___f_222_, 0, v___x_214_);
lean_closure_set(v___f_222_, 1, v_a_192_);
lean_closure_set(v___f_222_, 2, v___x_195_);
lean_closure_set(v___f_222_, 3, v_xs_185_);
lean_closure_set(v___f_222_, 4, v___x_196_);
lean_closure_set(v___f_222_, 5, v_a_194_);
lean_closure_set(v___f_222_, 6, v_a_213_);
lean_closure_set(v___f_222_, 7, v___x_197_);
lean_closure_set(v___f_222_, 8, v___x_198_);
lean_closure_set(v___f_222_, 9, v_00_u03b2_199_);
lean_closure_set(v___f_222_, 10, v___x_219_);
lean_closure_set(v___f_222_, 11, v___x_220_);
lean_closure_set(v___f_222_, 12, v___x_221_);
lean_closure_set(v___f_222_, 13, v___x_216_);
lean_closure_set(v___f_222_, 14, v_f_190_);
lean_closure_set(v___f_222_, 15, v_g_191_);
lean_closure_set(v___f_222_, 16, v_h_200_);
lean_closure_set(v___f_222_, 17, v___x_218_);
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3));
v___x_224_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_223_, v___x_218_, v___f_222_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
return v___x_224_;
}
else
{
lean_dec_ref(v_h_200_);
lean_dec_ref(v_00_u03b2_199_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec(v___x_195_);
lean_dec_ref(v_a_194_);
lean_dec(v___x_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_g_191_);
lean_dec_ref(v_f_190_);
lean_dec_ref(v_xs_185_);
return v___x_212_;
}
}
else
{
lean_dec_ref(v_h_200_);
lean_dec_ref(v_00_u03b2_199_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec(v___x_195_);
lean_dec_ref(v_a_194_);
lean_dec(v___x_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_g_191_);
lean_dec_ref(v_f_190_);
lean_dec_ref(v_xs_185_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed(lean_object** _args){
lean_object* v_xs_225_ = _args[0];
lean_object* v___x_226_ = _args[1];
lean_object* v___x_227_ = _args[2];
lean_object* v___x_228_ = _args[3];
lean_object* v___x_229_ = _args[4];
lean_object* v_f_230_ = _args[5];
lean_object* v_g_231_ = _args[6];
lean_object* v_a_232_ = _args[7];
lean_object* v___x_233_ = _args[8];
lean_object* v_a_234_ = _args[9];
lean_object* v___x_235_ = _args[10];
lean_object* v___x_236_ = _args[11];
lean_object* v___x_237_ = _args[12];
lean_object* v___x_238_ = _args[13];
lean_object* v_00_u03b2_239_ = _args[14];
lean_object* v_h_240_ = _args[15];
lean_object* v___y_241_ = _args[16];
lean_object* v___y_242_ = _args[17];
lean_object* v___y_243_ = _args[18];
lean_object* v___y_244_ = _args[19];
lean_object* v___y_245_ = _args[20];
_start:
{
uint8_t v___x_2195__boxed_246_; uint8_t v___x_2196__boxed_247_; uint8_t v___x_2197__boxed_248_; lean_object* v_res_249_; 
v___x_2195__boxed_246_ = lean_unbox(v___x_227_);
v___x_2196__boxed_247_ = lean_unbox(v___x_228_);
v___x_2197__boxed_248_ = lean_unbox(v___x_229_);
v_res_249_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(v_xs_225_, v___x_226_, v___x_2195__boxed_246_, v___x_2196__boxed_247_, v___x_2197__boxed_248_, v_f_230_, v_g_231_, v_a_232_, v___x_233_, v_a_234_, v___x_235_, v___x_236_, v___x_237_, v___x_238_, v_00_u03b2_239_, v_h_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(lean_object* v_a_256_, lean_object* v_f_257_, lean_object* v_xs_258_, lean_object* v_00_u03b2_259_, uint8_t v___x_260_, uint8_t v___x_261_, uint8_t v___x_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_g_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1));
v___x_274_ = lean_box(0);
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v_a_256_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
lean_inc_ref(v___x_275_);
v___x_276_ = l_Lean_mkConst(v___x_273_, v___x_275_);
lean_inc_ref(v_f_257_);
v___x_277_ = l_Lean_mkAppN(v_f_257_, v_xs_258_);
lean_inc_ref(v_g_267_);
v___x_278_ = l_Lean_mkAppN(v_g_267_, v_xs_258_);
lean_inc_ref(v_00_u03b2_259_);
v___x_279_ = l_Lean_mkApp3(v___x_276_, v_00_u03b2_259_, v___x_277_, v___x_278_);
lean_inc_ref(v___x_279_);
v___x_280_ = l_Lean_Meta_mkForallFVars(v_xs_258_, v___x_279_, v___x_260_, v___x_261_, v___x_261_, v___x_262_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v___x_280_);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3));
v___x_283_ = lean_box(v___x_260_);
v___x_284_ = lean_box(v___x_261_);
v___x_285_ = lean_box(v___x_262_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed), 21, 15);
lean_closure_set(v___f_286_, 0, v_xs_258_);
lean_closure_set(v___f_286_, 1, v___x_279_);
lean_closure_set(v___f_286_, 2, v___x_283_);
lean_closure_set(v___f_286_, 3, v___x_284_);
lean_closure_set(v___f_286_, 4, v___x_285_);
lean_closure_set(v___f_286_, 5, v_f_257_);
lean_closure_set(v___f_286_, 6, v_g_267_);
lean_closure_set(v___f_286_, 7, v_a_263_);
lean_closure_set(v___f_286_, 8, v___x_274_);
lean_closure_set(v___f_286_, 9, v_a_264_);
lean_closure_set(v___f_286_, 10, v___x_275_);
lean_closure_set(v___f_286_, 11, v___x_265_);
lean_closure_set(v___f_286_, 12, v___x_282_);
lean_closure_set(v___f_286_, 13, v___x_266_);
lean_closure_set(v___f_286_, 14, v_00_u03b2_259_);
v___x_287_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_282_, v_a_281_, v___f_286_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_287_;
}
else
{
lean_dec_ref(v___x_279_);
lean_dec_ref(v___x_275_);
lean_dec_ref(v_g_267_);
lean_dec(v___x_266_);
lean_dec(v___x_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_00_u03b2_259_);
lean_dec_ref(v_xs_258_);
lean_dec_ref(v_f_257_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed(lean_object** _args){
lean_object* v_a_288_ = _args[0];
lean_object* v_f_289_ = _args[1];
lean_object* v_xs_290_ = _args[2];
lean_object* v_00_u03b2_291_ = _args[3];
lean_object* v___x_292_ = _args[4];
lean_object* v___x_293_ = _args[5];
lean_object* v___x_294_ = _args[6];
lean_object* v_a_295_ = _args[7];
lean_object* v_a_296_ = _args[8];
lean_object* v___x_297_ = _args[9];
lean_object* v___x_298_ = _args[10];
lean_object* v_g_299_ = _args[11];
lean_object* v___y_300_ = _args[12];
lean_object* v___y_301_ = _args[13];
lean_object* v___y_302_ = _args[14];
lean_object* v___y_303_ = _args[15];
lean_object* v___y_304_ = _args[16];
_start:
{
uint8_t v___x_2301__boxed_305_; uint8_t v___x_2302__boxed_306_; uint8_t v___x_2303__boxed_307_; lean_object* v_res_308_; 
v___x_2301__boxed_305_ = lean_unbox(v___x_292_);
v___x_2302__boxed_306_ = lean_unbox(v___x_293_);
v___x_2303__boxed_307_ = lean_unbox(v___x_294_);
v_res_308_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(v_a_288_, v_f_289_, v_xs_290_, v_00_u03b2_291_, v___x_2301__boxed_305_, v___x_2302__boxed_306_, v___x_2303__boxed_307_, v_a_295_, v_a_296_, v___x_297_, v___x_298_, v_g_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(lean_object* v_a_312_, lean_object* v_xs_313_, lean_object* v_00_u03b2_314_, uint8_t v___x_315_, uint8_t v___x_316_, uint8_t v___x_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v___x_320_, lean_object* v_f_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___f_331_; lean_object* v___x_332_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1));
v___x_328_ = lean_box(v___x_315_);
v___x_329_ = lean_box(v___x_316_);
v___x_330_ = lean_box(v___x_317_);
lean_inc_ref(v_a_319_);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed), 17, 11);
lean_closure_set(v___f_331_, 0, v_a_312_);
lean_closure_set(v___f_331_, 1, v_f_321_);
lean_closure_set(v___f_331_, 2, v_xs_313_);
lean_closure_set(v___f_331_, 3, v_00_u03b2_314_);
lean_closure_set(v___f_331_, 4, v___x_328_);
lean_closure_set(v___f_331_, 5, v___x_329_);
lean_closure_set(v___f_331_, 6, v___x_330_);
lean_closure_set(v___f_331_, 7, v_a_318_);
lean_closure_set(v___f_331_, 8, v_a_319_);
lean_closure_set(v___f_331_, 9, v___x_320_);
lean_closure_set(v___f_331_, 10, v___x_327_);
v___x_332_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_327_, v_a_319_, v___f_331_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed(lean_object* v_a_333_, lean_object* v_xs_334_, lean_object* v_00_u03b2_335_, lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v___x_341_, lean_object* v_f_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v___x_2383__boxed_348_; uint8_t v___x_2384__boxed_349_; uint8_t v___x_2385__boxed_350_; lean_object* v_res_351_; 
v___x_2383__boxed_348_ = lean_unbox(v___x_336_);
v___x_2384__boxed_349_ = lean_unbox(v___x_337_);
v___x_2385__boxed_350_ = lean_unbox(v___x_338_);
v_res_351_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(v_a_333_, v_xs_334_, v_00_u03b2_335_, v___x_2383__boxed_348_, v___x_2384__boxed_349_, v___x_2385__boxed_350_, v_a_339_, v_a_340_, v___x_341_, v_f_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(lean_object* v_xs_355_, lean_object* v_00_u03b2_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
uint8_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; 
v___x_362_ = 0;
v___x_363_ = 1;
v___x_364_ = 1;
lean_inc_ref(v_00_u03b2_356_);
v___x_365_ = l_Lean_Meta_mkForallFVars(v_xs_355_, v_00_u03b2_356_, v___x_362_, v___x_363_, v___x_363_, v___x_364_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_367_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref(v___x_365_);
lean_inc_ref(v_00_u03b2_356_);
v___x_367_ = l_Lean_Meta_getLevel(v_00_u03b2_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref(v___x_367_);
lean_inc(v_a_366_);
v___x_369_ = l_Lean_Meta_getLevel(v_a_366_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_369_);
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1));
v___x_372_ = lean_box(v___x_362_);
v___x_373_ = lean_box(v___x_363_);
v___x_374_ = lean_box(v___x_364_);
lean_inc(v_a_366_);
v___f_375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed), 15, 9);
lean_closure_set(v___f_375_, 0, v_a_368_);
lean_closure_set(v___f_375_, 1, v_xs_355_);
lean_closure_set(v___f_375_, 2, v_00_u03b2_356_);
lean_closure_set(v___f_375_, 3, v___x_372_);
lean_closure_set(v___f_375_, 4, v___x_373_);
lean_closure_set(v___f_375_, 5, v___x_374_);
lean_closure_set(v___f_375_, 6, v_a_370_);
lean_closure_set(v___f_375_, 7, v_a_366_);
lean_closure_set(v___f_375_, 8, v___x_371_);
v___x_376_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_371_, v_a_366_, v___f_375_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_a_368_);
lean_dec(v_a_366_);
lean_dec_ref(v_00_u03b2_356_);
lean_dec_ref(v_xs_355_);
v_a_377_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_369_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_369_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_366_);
lean_dec_ref(v_00_u03b2_356_);
lean_dec_ref(v_xs_355_);
v_a_385_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_367_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_367_);
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
lean_dec_ref(v_00_u03b2_356_);
lean_dec_ref(v_xs_355_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___boxed(lean_object* v_xs_393_, lean_object* v_00_u03b2_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_393_, v_00_u03b2_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_name_402_, uint8_t v_bi_403_, lean_object* v_type_404_, lean_object* v_k_405_, uint8_t v_kind_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_402_, v_bi_403_, v_type_404_, v_k_405_, v_kind_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_name_414_, lean_object* v_bi_415_, lean_object* v_type_416_, lean_object* v_k_417_, lean_object* v_kind_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v_bi_boxed_424_; uint8_t v_kind_boxed_425_; lean_object* v_res_426_; 
v_bi_boxed_424_ = lean_unbox(v_bi_415_);
v_kind_boxed_425_ = lean_unbox(v_kind_418_);
v_res_426_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(v_00_u03b1_413_, v_name_414_, v_bi_boxed_424_, v_type_416_, v_k_417_, v_kind_boxed_425_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(lean_object* v_00_u03b1_427_, lean_object* v_name_428_, lean_object* v_type_429_, lean_object* v_k_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_428_, v_type_429_, v_k_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___boxed(lean_object* v_00_u03b1_437_, lean_object* v_name_438_, lean_object* v_type_439_, lean_object* v_k_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(v_00_u03b1_437_, v_name_438_, v_type_439_, v_k_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_447_, lean_object* v_vals_448_, lean_object* v_i_449_, lean_object* v_k_450_){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_array_get_size(v_keys_447_);
v___x_452_ = lean_nat_dec_lt(v_i_449_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_i_449_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_k_x27_454_; uint8_t v___x_455_; 
v_k_x27_454_ = lean_array_fget_borrowed(v_keys_447_, v_i_449_);
v___x_455_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_450_, v_k_x27_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_nat_add(v_i_449_, v___x_456_);
lean_dec(v_i_449_);
v_i_449_ = v___x_457_;
goto _start;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_array_fget_borrowed(v_vals_448_, v_i_449_);
lean_dec(v_i_449_);
lean_inc(v___x_459_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_461_, lean_object* v_vals_462_, lean_object* v_i_463_, lean_object* v_k_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_461_, v_vals_462_, v_i_463_, v_k_464_);
lean_dec_ref(v_k_464_);
lean_dec_ref(v_vals_462_);
lean_dec_ref(v_keys_461_);
return v_res_465_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; 
v___x_466_ = ((size_t)5ULL);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_shift_left(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; 
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__0);
v___x_471_ = lean_usize_sub(v___x_470_, v___x_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(lean_object* v_x_472_, size_t v_x_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v_es_475_; lean_object* v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v_j_480_; lean_object* v___x_481_; 
v_es_475_ = lean_ctor_get(v_x_472_, 0);
v___x_476_ = lean_box(2);
v___x_477_ = ((size_t)5ULL);
v___x_478_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1);
v___x_479_ = lean_usize_land(v_x_473_, v___x_478_);
v_j_480_ = lean_usize_to_nat(v___x_479_);
v___x_481_ = lean_array_get_borrowed(v___x_476_, v_es_475_, v_j_480_);
lean_dec(v_j_480_);
switch(lean_obj_tag(v___x_481_))
{
case 0:
{
lean_object* v_key_482_; lean_object* v_val_483_; uint8_t v___x_484_; 
v_key_482_ = lean_ctor_get(v___x_481_, 0);
v_val_483_ = lean_ctor_get(v___x_481_, 1);
v___x_484_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_474_, v_key_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
v___x_485_ = lean_box(0);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
lean_inc(v_val_483_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v_val_483_);
return v___x_486_;
}
}
case 1:
{
lean_object* v_node_487_; size_t v___x_488_; 
v_node_487_ = lean_ctor_get(v___x_481_, 0);
v___x_488_ = lean_usize_shift_right(v_x_473_, v___x_477_);
v_x_472_ = v_node_487_;
v_x_473_ = v___x_488_;
goto _start;
}
default: 
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
return v___x_490_;
}
}
}
else
{
lean_object* v_ks_491_; lean_object* v_vs_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_ks_491_ = lean_ctor_get(v_x_472_, 0);
v_vs_492_ = lean_ctor_get(v_x_472_, 1);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_ks_491_, v_vs_492_, v___x_493_, v_x_474_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
size_t v_x_6888__boxed_498_; lean_object* v_res_499_; 
v_x_6888__boxed_498_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_res_499_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_495_, v_x_6888__boxed_498_, v_x_497_);
lean_dec_ref(v_x_497_);
lean_dec_ref(v_x_495_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
uint64_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_501_);
v___x_503_ = lean_uint64_to_usize(v___x_502_);
v___x_504_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_500_, v___x_503_, v_x_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_505_, v_x_506_);
lean_dec_ref(v_x_506_);
lean_dec_ref(v_x_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_ks_512_; lean_object* v_vs_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_537_; 
v_ks_512_ = lean_ctor_get(v_x_508_, 0);
v_vs_513_ = lean_ctor_get(v_x_508_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_537_ == 0)
{
v___x_515_ = v_x_508_;
v_isShared_516_ = v_isSharedCheck_537_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_vs_513_);
lean_inc(v_ks_512_);
lean_dec(v_x_508_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_537_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_ks_512_);
v___x_518_ = lean_nat_dec_lt(v_x_509_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_x_509_);
v___x_519_ = lean_array_push(v_ks_512_, v_x_510_);
v___x_520_ = lean_array_push(v_vs_513_, v_x_511_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_520_);
lean_ctor_set(v___x_515_, 0, v___x_519_);
v___x_522_ = v___x_515_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v_k_x27_524_; uint8_t v___x_525_; 
v_k_x27_524_ = lean_array_fget_borrowed(v_ks_512_, v_x_509_);
v___x_525_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_510_, v_k_x27_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_527_; 
if (v_isShared_516_ == 0)
{
v___x_527_ = v___x_515_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_ks_512_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_vs_513_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_x_509_, v___x_528_);
lean_dec(v_x_509_);
v_x_508_ = v___x_527_;
v_x_509_ = v___x_529_;
goto _start;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_array_fset(v_ks_512_, v_x_509_, v_x_510_);
v___x_533_ = lean_array_fset(v_vs_513_, v_x_509_, v_x_511_);
lean_dec(v_x_509_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_533_);
lean_ctor_set(v___x_515_, 0, v___x_532_);
v___x_535_ = v___x_515_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(lean_object* v_n_538_, lean_object* v_k_539_, lean_object* v_v_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_n_538_, v___x_541_, v_k_539_, v_v_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(lean_object* v_x_544_, size_t v_x_545_, size_t v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_es_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v_j_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_es_549_ = lean_ctor_get(v_x_544_, 0);
v___x_550_ = ((size_t)5ULL);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___closed__1);
v___x_553_ = lean_usize_land(v_x_545_, v___x_552_);
v_j_554_ = lean_usize_to_nat(v___x_553_);
v___x_555_ = lean_array_get_size(v_es_549_);
v___x_556_ = lean_nat_dec_lt(v_j_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_j_554_);
lean_dec(v_x_548_);
lean_dec_ref(v_x_547_);
return v_x_544_;
}
else
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_593_; 
lean_inc_ref(v_es_549_);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v_x_544_, 0);
lean_dec(v_unused_594_);
v___x_558_ = v_x_544_;
v_isShared_559_ = v_isSharedCheck_593_;
goto v_resetjp_557_;
}
else
{
lean_dec(v_x_544_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_593_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_v_560_; lean_object* v___x_561_; lean_object* v_xs_x27_562_; lean_object* v___y_564_; 
v_v_560_ = lean_array_fget(v_es_549_, v_j_554_);
v___x_561_ = lean_box(0);
v_xs_x27_562_ = lean_array_fset(v_es_549_, v_j_554_, v___x_561_);
switch(lean_obj_tag(v_v_560_))
{
case 0:
{
lean_object* v_key_569_; lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_580_; 
v_key_569_ = lean_ctor_get(v_v_560_, 0);
v_val_570_ = lean_ctor_get(v_v_560_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_v_560_);
if (v_isSharedCheck_580_ == 0)
{
v___x_572_ = v_v_560_;
v_isShared_573_ = v_isSharedCheck_580_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_inc(v_key_569_);
lean_dec(v_v_560_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_580_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
uint8_t v___x_574_; 
v___x_574_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_547_, v_key_569_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_del_object(v___x_572_);
v___x_575_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_569_, v_val_570_, v_x_547_, v_x_548_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___y_564_ = v___x_576_;
goto v___jp_563_;
}
else
{
lean_object* v___x_578_; 
lean_dec(v_val_570_);
lean_dec(v_key_569_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v_x_548_);
lean_ctor_set(v___x_572_, 0, v_x_547_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_x_547_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_x_548_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v___y_564_ = v___x_578_;
goto v___jp_563_;
}
}
}
}
case 1:
{
lean_object* v_node_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_591_; 
v_node_581_ = lean_ctor_get(v_v_560_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_v_560_);
if (v_isSharedCheck_591_ == 0)
{
v___x_583_ = v_v_560_;
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_node_581_);
lean_dec(v_v_560_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_585_ = lean_usize_shift_right(v_x_545_, v___x_550_);
v___x_586_ = lean_usize_add(v_x_546_, v___x_551_);
v___x_587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_node_581_, v___x_585_, v___x_586_, v_x_547_, v_x_548_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_587_);
v___x_589_ = v___x_583_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
v___y_564_ = v___x_589_;
goto v___jp_563_;
}
}
}
default: 
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_x_547_);
lean_ctor_set(v___x_592_, 1, v_x_548_);
v___y_564_ = v___x_592_;
goto v___jp_563_;
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_array_fset(v_xs_x27_562_, v_j_554_, v___y_564_);
lean_dec(v_j_554_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_565_);
v___x_567_ = v___x_558_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
else
{
lean_object* v_ks_595_; lean_object* v_vs_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_616_; 
v_ks_595_ = lean_ctor_get(v_x_544_, 0);
v_vs_596_ = lean_ctor_get(v_x_544_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_616_ == 0)
{
v___x_598_ = v_x_544_;
v_isShared_599_ = v_isSharedCheck_616_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_vs_596_);
lean_inc(v_ks_595_);
lean_dec(v_x_544_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_616_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_ks_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_vs_596_);
v___x_601_ = v_reuseFailAlloc_615_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v_newNode_602_; uint8_t v___y_604_; size_t v___x_610_; uint8_t v___x_611_; 
v_newNode_602_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v___x_601_, v_x_547_, v_x_548_);
v___x_610_ = ((size_t)7ULL);
v___x_611_ = lean_usize_dec_le(v___x_610_, v_x_546_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_602_);
v___x_613_ = lean_unsigned_to_nat(4u);
v___x_614_ = lean_nat_dec_lt(v___x_612_, v___x_613_);
lean_dec(v___x_612_);
v___y_604_ = v___x_614_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_611_;
goto v___jp_603_;
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
lean_object* v_ks_605_; lean_object* v_vs_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_ks_605_ = lean_ctor_get(v_newNode_602_, 0);
lean_inc_ref(v_ks_605_);
v_vs_606_ = lean_ctor_get(v_newNode_602_, 1);
lean_inc_ref(v_vs_606_);
lean_dec_ref(v_newNode_602_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0);
v___x_609_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_x_546_, v_ks_605_, v_vs_606_, v___x_607_, v___x_608_);
lean_dec_ref(v_vs_606_);
lean_dec_ref(v_ks_605_);
return v___x_609_;
}
else
{
return v_newNode_602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(size_t v_depth_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_i_620_, lean_object* v_entries_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_keys_618_);
v___x_623_ = lean_nat_dec_lt(v_i_620_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec(v_i_620_);
return v_entries_621_;
}
else
{
lean_object* v_k_624_; lean_object* v_v_625_; uint64_t v___x_626_; size_t v_h_627_; size_t v___x_628_; lean_object* v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v_h_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_k_624_ = lean_array_fget_borrowed(v_keys_618_, v_i_620_);
v_v_625_ = lean_array_fget_borrowed(v_vals_619_, v_i_620_);
v___x_626_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_624_);
v_h_627_ = lean_uint64_to_usize(v___x_626_);
v___x_628_ = ((size_t)5ULL);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_sub(v_depth_617_, v___x_630_);
v___x_632_ = lean_usize_mul(v___x_628_, v___x_631_);
v_h_633_ = lean_usize_shift_right(v_h_627_, v___x_632_);
v___x_634_ = lean_nat_add(v_i_620_, v___x_629_);
lean_dec(v_i_620_);
lean_inc(v_v_625_);
lean_inc(v_k_624_);
v___x_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_entries_621_, v_h_633_, v_depth_617_, v_k_624_, v_v_625_);
v_i_620_ = v___x_634_;
v_entries_621_ = v___x_635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_637_, lean_object* v_keys_638_, lean_object* v_vals_639_, lean_object* v_i_640_, lean_object* v_entries_641_){
_start:
{
size_t v_depth_boxed_642_; lean_object* v_res_643_; 
v_depth_boxed_642_ = lean_unbox_usize(v_depth_637_);
lean_dec(v_depth_637_);
v_res_643_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_boxed_642_, v_keys_638_, v_vals_639_, v_i_640_, v_entries_641_);
lean_dec_ref(v_vals_639_);
lean_dec_ref(v_keys_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
size_t v_x_7035__boxed_649_; size_t v_x_7036__boxed_650_; lean_object* v_res_651_; 
v_x_7035__boxed_649_ = lean_unbox_usize(v_x_645_);
lean_dec(v_x_645_);
v_x_7036__boxed_650_ = lean_unbox_usize(v_x_646_);
lean_dec(v_x_646_);
v_res_651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_644_, v_x_7035__boxed_649_, v_x_7036__boxed_650_, v_x_647_, v_x_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
uint64_t v___x_655_; size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_655_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_653_);
v___x_656_ = lean_uint64_to_usize(v___x_655_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_652_, v___x_656_, v___x_657_, v_x_653_, v_x_654_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(lean_object* v_e_659_, lean_object* v_xs_660_, lean_object* v_b_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; 
lean_inc(v_a_666_);
lean_inc_ref(v_a_665_);
lean_inc(v_a_664_);
lean_inc_ref(v_a_663_);
v___x_668_ = lean_infer_type(v_e_659_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_705_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_705_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_705_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_705_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v_funext_674_; lean_object* v___x_675_; 
v___x_673_ = lean_st_ref_get(v_a_662_);
v_funext_674_ = lean_ctor_get(v___x_673_, 3);
lean_inc_ref(v_funext_674_);
lean_dec(v___x_673_);
v___x_675_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_funext_674_, v_a_669_);
lean_dec_ref(v_funext_674_);
if (lean_obj_tag(v___x_675_) == 1)
{
lean_object* v_val_676_; lean_object* v___x_678_; 
lean_dec(v_a_669_);
lean_dec_ref(v_b_661_);
lean_dec_ref(v_xs_660_);
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref(v___x_675_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v_val_676_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_val_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v___x_675_);
lean_del_object(v___x_671_);
lean_inc(v_a_666_);
lean_inc_ref(v_a_665_);
lean_inc(v_a_664_);
lean_inc_ref(v_a_663_);
v___x_680_ = lean_infer_type(v_b_661_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v___x_682_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_660_, v_a_681_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_704_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_704_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v_numSteps_688_; lean_object* v_persistentCache_689_; lean_object* v_transientCache_690_; lean_object* v_funext_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_703_; 
v___x_687_ = lean_st_ref_take(v_a_662_);
v_numSteps_688_ = lean_ctor_get(v___x_687_, 0);
v_persistentCache_689_ = lean_ctor_get(v___x_687_, 1);
v_transientCache_690_ = lean_ctor_get(v___x_687_, 2);
v_funext_691_ = lean_ctor_get(v___x_687_, 3);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_703_ == 0)
{
v___x_693_ = v___x_687_;
v_isShared_694_ = v_isSharedCheck_703_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_funext_691_);
lean_inc(v_transientCache_690_);
lean_inc(v_persistentCache_689_);
lean_inc(v_numSteps_688_);
lean_dec(v___x_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_703_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_inc(v_a_683_);
v___x_695_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_funext_691_, v_a_669_, v_a_683_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 3, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_numSteps_688_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_persistentCache_689_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_transientCache_690_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v___x_695_);
v___x_697_ = v_reuseFailAlloc_702_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_st_ref_set(v_a_662_, v___x_697_);
if (v_isShared_686_ == 0)
{
v___x_700_ = v___x_685_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_683_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
else
{
lean_dec(v_a_669_);
return v___x_682_;
}
}
else
{
lean_dec(v_a_669_);
lean_dec_ref(v_xs_660_);
return v___x_680_;
}
}
}
}
else
{
lean_dec_ref(v_b_661_);
lean_dec_ref(v_xs_660_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(lean_object* v_e_706_, lean_object* v_xs_707_, lean_object* v_b_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_706_, v_xs_707_, v_b_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(lean_object* v_e_716_, lean_object* v_xs_717_, lean_object* v_b_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_716_, v_xs_717_, v_b_718_, v_a_721_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(lean_object* v_e_730_, lean_object* v_xs_731_, lean_object* v_b_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(v_e_730_, v_xs_731_, v_b_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(lean_object* v_00_u03b2_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_745_, v_x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(lean_object* v_00_u03b2_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(v_00_u03b2_748_, v_x_749_, v_x_750_);
lean_dec_ref(v_x_750_);
lean_dec_ref(v_x_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_x_753_, v_x_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_object* v_00_u03b2_757_, lean_object* v_x_758_, size_t v_x_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_758_, v_x_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
size_t v_x_7298__boxed_766_; lean_object* v_res_767_; 
v_x_7298__boxed_766_ = lean_unbox_usize(v_x_764_);
lean_dec(v_x_764_);
v_res_767_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(v_00_u03b2_762_, v_x_763_, v_x_7298__boxed_766_, v_x_765_);
lean_dec_ref(v_x_765_);
lean_dec_ref(v_x_763_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, size_t v_x_770_, size_t v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_769_, v_x_770_, v_x_771_, v_x_772_, v_x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
size_t v_x_7309__boxed_781_; size_t v_x_7310__boxed_782_; lean_object* v_res_783_; 
v_x_7309__boxed_781_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_x_7310__boxed_782_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_res_783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(v_00_u03b2_775_, v_x_776_, v_x_7309__boxed_781_, v_x_7310__boxed_782_, v_x_779_, v_x_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_784_, lean_object* v_keys_785_, lean_object* v_vals_786_, lean_object* v_heq_787_, lean_object* v_i_788_, lean_object* v_k_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_785_, v_vals_786_, v_i_788_, v_k_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_791_, lean_object* v_keys_792_, lean_object* v_vals_793_, lean_object* v_heq_794_, lean_object* v_i_795_, lean_object* v_k_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(v_00_u03b2_791_, v_keys_792_, v_vals_793_, v_heq_794_, v_i_795_, v_k_796_);
lean_dec_ref(v_k_796_);
lean_dec_ref(v_vals_793_);
lean_dec_ref(v_keys_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_798_, lean_object* v_n_799_, lean_object* v_k_800_, lean_object* v_v_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v_n_799_, v_k_800_, v_v_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_803_, size_t v_depth_804_, lean_object* v_keys_805_, lean_object* v_vals_806_, lean_object* v_heq_807_, lean_object* v_i_808_, lean_object* v_entries_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_804_, v_keys_805_, v_vals_806_, v_i_808_, v_entries_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_811_, lean_object* v_depth_812_, lean_object* v_keys_813_, lean_object* v_vals_814_, lean_object* v_heq_815_, lean_object* v_i_816_, lean_object* v_entries_817_){
_start:
{
size_t v_depth_boxed_818_; lean_object* v_res_819_; 
v_depth_boxed_818_ = lean_unbox_usize(v_depth_812_);
lean_dec(v_depth_812_);
v_res_819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(v_00_u03b2_811_, v_depth_boxed_818_, v_keys_813_, v_vals_814_, v_heq_815_, v_i_816_, v_entries_817_);
lean_dec_ref(v_vals_814_);
lean_dec_ref(v_keys_813_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_x_821_, v_x_822_, v_x_823_, v_x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(lean_object* v_simpBody_826_, lean_object* v_e_827_, lean_object* v_xs_828_, lean_object* v_b_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
lean_inc(v_a_838_);
lean_inc_ref(v_a_837_);
lean_inc(v_a_836_);
lean_inc_ref(v_a_835_);
lean_inc(v_a_834_);
lean_inc_ref(v_a_833_);
lean_inc(v_a_832_);
lean_inc_ref(v_a_831_);
lean_inc(v_a_830_);
lean_inc_ref(v_b_829_);
v___x_840_ = lean_apply_11(v_simpBody_826_, v_b_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, lean_box(0));
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_911_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_911_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_911_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_911_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
if (lean_obj_tag(v_a_841_) == 0)
{
uint8_t v_contextDependent_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec_ref(v_b_829_);
lean_dec_ref(v_xs_828_);
lean_dec_ref(v_e_827_);
v_contextDependent_845_ = lean_ctor_get_uint8(v_a_841_, 1);
lean_dec_ref(v_a_841_);
v___x_846_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_845_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v_e_x27_850_; lean_object* v_proof_851_; uint8_t v_contextDependent_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_843_);
v_e_x27_850_ = lean_ctor_get(v_a_841_, 0);
v_proof_851_ = lean_ctor_get(v_a_841_, 1);
v_contextDependent_852_ = lean_ctor_get_uint8(v_a_841_, sizeof(void*)*2 + 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_910_ == 0)
{
v___x_854_ = v_a_841_;
v_isShared_855_ = v_isSharedCheck_910_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_proof_851_);
lean_inc(v_e_x27_850_);
lean_dec(v_a_841_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_910_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; 
v___x_856_ = 0;
v___x_857_ = 1;
v___x_858_ = 1;
v___x_859_ = l_Lean_Meta_mkLambdaFVars(v_xs_828_, v_proof_851_, v___x_856_, v___x_857_, v___x_856_, v___x_857_, v___x_858_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
v___x_861_ = l_Lean_Meta_mkLambdaFVars(v_xs_828_, v_e_x27_850_, v___x_856_, v___x_857_, v___x_856_, v___x_857_, v___x_858_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___x_863_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_862_, v_a_834_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
lean_inc_ref(v_e_827_);
v___x_865_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_827_, v_xs_828_, v_b_829_, v_a_832_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_877_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_inc(v_a_864_);
v___x_870_ = l_Lean_mkApp3(v_a_866_, v_e_827_, v_a_864_, v_a_860_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_870_);
lean_ctor_set(v___x_854_, 0, v_a_864_);
v___x_872_ = v___x_854_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*2 + 1, v_contextDependent_852_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*2, v___x_856_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_872_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_864_);
lean_dec(v_a_860_);
lean_del_object(v___x_854_);
lean_dec_ref(v_e_827_);
v_a_878_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_865_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_865_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_860_);
lean_del_object(v___x_854_);
lean_dec_ref(v_b_829_);
lean_dec_ref(v_xs_828_);
lean_dec_ref(v_e_827_);
v_a_886_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_863_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_863_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_a_860_);
lean_del_object(v___x_854_);
lean_dec_ref(v_b_829_);
lean_dec_ref(v_xs_828_);
lean_dec_ref(v_e_827_);
v_a_894_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_861_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_861_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_del_object(v___x_854_);
lean_dec_ref(v_e_x27_850_);
lean_dec_ref(v_b_829_);
lean_dec_ref(v_xs_828_);
lean_dec_ref(v_e_827_);
v_a_902_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_859_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_859_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_829_);
lean_dec_ref(v_xs_828_);
lean_dec_ref(v_e_827_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(lean_object* v_simpBody_912_, lean_object* v_e_913_, lean_object* v_xs_914_, lean_object* v_b_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_912_, v_e_913_, v_xs_914_, v_b_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(lean_object* v_k_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v_b_933_, lean_object* v_c_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
v___x_940_ = lean_apply_12(v_k_927_, v_b_933_, v_c_934_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, lean_box(0));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v_b_947_, lean_object* v_c_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(v_k_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v_b_947_, v_c_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(lean_object* v_e_955_, lean_object* v_k_956_, uint8_t v_cleanupAnnotations_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___f_968_; uint8_t v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_968_, 0, v_k_956_);
lean_closure_set(v___f_968_, 1, v___y_958_);
lean_closure_set(v___f_968_, 2, v___y_959_);
lean_closure_set(v___f_968_, 3, v___y_960_);
lean_closure_set(v___f_968_, 4, v___y_961_);
lean_closure_set(v___f_968_, 5, v___y_962_);
v___x_969_ = 1;
v___x_970_ = 0;
v___x_971_ = lean_box(0);
v___x_972_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_955_, v___x_969_, v___x_970_, v___x_969_, v___x_970_, v___x_971_, v___f_968_, v_cleanupAnnotations_957_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_972_) == 0)
{
return v___x_972_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(lean_object* v_e_981_, lean_object* v_k_982_, lean_object* v_cleanupAnnotations_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_994_; lean_object* v_res_995_; 
v_cleanupAnnotations_boxed_994_ = lean_unbox(v_cleanupAnnotations_983_);
v_res_995_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_981_, v_k_982_, v_cleanupAnnotations_boxed_994_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_object* v_00_u03b1_996_, lean_object* v_e_997_, lean_object* v_k_998_, uint8_t v_cleanupAnnotations_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_997_, v_k_998_, v_cleanupAnnotations_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_e_1012_, lean_object* v_k_1013_, lean_object* v_cleanupAnnotations_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1025_; lean_object* v_res_1026_; 
v_cleanupAnnotations_boxed_1025_ = lean_unbox(v_cleanupAnnotations_1014_);
v_res_1026_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(v_00_u03b1_1011_, v_e_1012_, v_k_1013_, v_cleanupAnnotations_boxed_1025_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(lean_object* v___y_1027_, lean_object* v_transientCache_1028_, lean_object* v_funext_1029_, lean_object* v_a_x3f_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v_numSteps_1033_; lean_object* v_persistentCache_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1044_; 
v___x_1032_ = lean_st_ref_take(v___y_1027_);
v_numSteps_1033_ = lean_ctor_get(v___x_1032_, 0);
v_persistentCache_1034_ = lean_ctor_get(v___x_1032_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; lean_object* v_unused_1046_; 
v_unused_1045_ = lean_ctor_get(v___x_1032_, 3);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v___x_1032_, 2);
lean_dec(v_unused_1046_);
v___x_1036_ = v___x_1032_;
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_persistentCache_1034_);
lean_inc(v_numSteps_1033_);
lean_dec(v___x_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 3, v_funext_1029_);
lean_ctor_set(v___x_1036_, 2, v_transientCache_1028_);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_numSteps_1033_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_persistentCache_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_transientCache_1028_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_funext_1029_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_st_ref_set(v___y_1027_, v___x_1039_);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(lean_object* v___y_1047_, lean_object* v_transientCache_1048_, lean_object* v_funext_1049_, lean_object* v_a_x3f_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1047_, v_transientCache_1048_, v_funext_1049_, v_a_x3f_1050_);
lean_dec(v_a_x3f_1050_);
lean_dec(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(lean_object* v_simpBody_1053_, lean_object* v_e_1054_, lean_object* v_xs_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_transientCache_1069_; lean_object* v_funext_1070_; lean_object* v_a_1072_; lean_object* v___x_1083_; 
v___x_1067_ = lean_st_ref_get(v___y_1059_);
v___x_1068_ = lean_st_ref_get(v___y_1059_);
v_transientCache_1069_ = lean_ctor_get(v___x_1067_, 2);
lean_inc_ref(v_transientCache_1069_);
lean_dec(v___x_1067_);
v_funext_1070_ = lean_ctor_get(v___x_1068_, 3);
lean_inc_ref(v_funext_1070_);
lean_dec(v___x_1068_);
v___x_1083_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_1056_, v___y_1061_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_1053_, v_e_1054_, v_xs_1055_, v_a_1084_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1102_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1102_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1102_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
lean_inc(v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v___x_1092_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1059_, v_transientCache_1069_, v_funext_1070_, v___x_1091_);
lean_dec_ref(v___x_1091_);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1100_);
v___x_1094_ = v___x_1092_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___x_1092_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_a_1086_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1086_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1085_);
v_a_1072_ = v_a_1103_;
goto v___jp_1071_;
}
}
else
{
lean_object* v_a_1104_; 
lean_dec_ref(v_xs_1055_);
lean_dec_ref(v_e_1054_);
lean_dec_ref(v_simpBody_1053_);
v_a_1104_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1104_);
lean_dec_ref(v___x_1083_);
v_a_1072_ = v_a_1104_;
goto v___jp_1071_;
}
v___jp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1059_, v_transientCache_1069_, v_funext_1070_, v___x_1073_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1074_, 0);
lean_dec(v_unused_1082_);
v___x_1076_ = v___x_1074_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v___x_1074_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 1);
lean_ctor_set(v___x_1076_, 0, v_a_1072_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1072_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(lean_object* v_simpBody_1105_, lean_object* v_e_1106_, lean_object* v_xs_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(v_simpBody_1105_, v_e_1106_, v_xs_1107_, v_b_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27(lean_object* v_simpBody_1120_, lean_object* v_e_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___f_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; 
lean_inc_ref(v_e_1121_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed), 14, 2);
lean_closure_set(v___f_1132_, 0, v_simpBody_1120_);
lean_closure_set(v___f_1132_, 1, v_e_1121_);
v___x_1133_ = 0;
v___x_1134_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1121_, v___f_1132_, v___x_1133_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(lean_object* v_simpBody_1135_, lean_object* v_e_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v_simpBody_1135_, v_e_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object* v_e_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLambda___closed__0));
v___x_1161_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v___x_1160_, v_e_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object* v_e_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
return v_res_1173_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
}
#ifdef __cplusplus
}
#endif
