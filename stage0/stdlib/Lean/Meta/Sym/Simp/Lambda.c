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
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(lean_object* v___x_11_, lean_object* v_a_12_, lean_object* v___x_13_, lean_object* v_xs_14_, lean_object* v___x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v___x_18_, lean_object* v___x_19_, lean_object* v_00_u03b2_20_, uint8_t v___x_21_, uint8_t v___x_22_, uint8_t v___x_23_, lean_object* v___x_24_, lean_object* v_f_25_, lean_object* v_g_26_, lean_object* v_h_27_, lean_object* v___x_28_, lean_object* v_f_x27_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
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
lean_dec_ref_known(v___x_53_, 1);
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_11_ = stack[0].m_obj;
lean_object* v_a_12_ = stack[1].m_obj;
lean_object* v___x_13_ = stack[2].m_obj;
lean_object* v_xs_14_ = stack[3].m_obj;
lean_object* v___x_15_ = stack[4].m_obj;
lean_object* v_a_16_ = stack[5].m_obj;
lean_object* v_a_17_ = stack[6].m_obj;
lean_object* v___x_18_ = stack[7].m_obj;
lean_object* v___x_19_ = stack[8].m_obj;
lean_object* v_00_u03b2_20_ = stack[9].m_obj;
uint8_t v___x_21_ = stack[10].m_num;
uint8_t v___x_22_ = stack[11].m_num;
uint8_t v___x_23_ = stack[12].m_num;
lean_object* v___x_24_ = stack[13].m_obj;
lean_object* v_f_25_ = stack[14].m_obj;
lean_object* v_g_26_ = stack[15].m_obj;
lean_object* v_h_27_ = stack[16].m_obj;
lean_object* v___x_28_ = stack[17].m_obj;
lean_object* v_f_x27_29_ = stack[18].m_obj;
lean_object* v___y_30_ = stack[19].m_obj;
lean_object* v___y_31_ = stack[20].m_obj;
lean_object* v___y_32_ = stack[21].m_obj;
lean_object* v___y_33_ = stack[22].m_obj;
lean_object* v_res_74_;
v_res_74_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(v___x_11_, v_a_12_, v___x_13_, v_xs_14_, v___x_15_, v_a_16_, v_a_17_, v___x_18_, v___x_19_, v_00_u03b2_20_, v___x_21_, v___x_22_, v___x_23_, v___x_24_, v_f_25_, v_g_26_, v_h_27_, v___x_28_, v_f_x27_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed(lean_object** _args){
lean_object* v___x_75_ = _args[0];
lean_object* v_a_76_ = _args[1];
lean_object* v___x_77_ = _args[2];
lean_object* v_xs_78_ = _args[3];
lean_object* v___x_79_ = _args[4];
lean_object* v_a_80_ = _args[5];
lean_object* v_a_81_ = _args[6];
lean_object* v___x_82_ = _args[7];
lean_object* v___x_83_ = _args[8];
lean_object* v_00_u03b2_84_ = _args[9];
lean_object* v___x_85_ = _args[10];
lean_object* v___x_86_ = _args[11];
lean_object* v___x_87_ = _args[12];
lean_object* v___x_88_ = _args[13];
lean_object* v_f_89_ = _args[14];
lean_object* v_g_90_ = _args[15];
lean_object* v_h_91_ = _args[16];
lean_object* v___x_92_ = _args[17];
lean_object* v_f_x27_93_ = _args[18];
lean_object* v___y_94_ = _args[19];
lean_object* v___y_95_ = _args[20];
lean_object* v___y_96_ = _args[21];
lean_object* v___y_97_ = _args[22];
lean_object* v___y_98_ = _args[23];
_start:
{
uint8_t v___x_1959__boxed_99_; uint8_t v___x_1960__boxed_100_; uint8_t v___x_1961__boxed_101_; lean_object* v_res_102_; 
v___x_1959__boxed_99_ = lean_unbox(v___x_85_);
v___x_1960__boxed_100_ = lean_unbox(v___x_86_);
v___x_1961__boxed_101_ = lean_unbox(v___x_87_);
v_res_102_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0(v___x_75_, v_a_76_, v___x_77_, v_xs_78_, v___x_79_, v_a_80_, v_a_81_, v___x_82_, v___x_83_, v_00_u03b2_84_, v___x_1959__boxed_99_, v___x_1960__boxed_100_, v___x_1961__boxed_101_, v___x_88_, v_f_89_, v_g_90_, v_h_91_, v___x_92_, v_f_x27_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec_ref(v_xs_78_);
return v_res_102_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(lean_object* v_k_103_, lean_object* v_b_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
v___x_110_ = lean_apply_6(v_k_103_, v_b_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, lean_box(0));
return v___x_110_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_103_ = stack[0].m_obj;
lean_object* v_b_104_ = stack[1].m_obj;
lean_object* v___y_105_ = stack[2].m_obj;
lean_object* v___y_106_ = stack[3].m_obj;
lean_object* v___y_107_ = stack[4].m_obj;
lean_object* v___y_108_ = stack[5].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(v_k_103_, v_b_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_112_, lean_object* v_b_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0(v_k_112_, v_b_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_119_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(lean_object* v_name_120_, uint8_t v_bi_121_, lean_object* v_type_122_, lean_object* v_k_123_, uint8_t v_kind_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; 
v___f_130_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_130_, 0, v_k_123_);
v___x_131_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_120_, v_bi_121_, v_type_122_, v___f_130_, v_kind_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_131_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_131_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_120_ = stack[0].m_obj;
uint8_t v_bi_121_ = stack[1].m_num;
lean_object* v_type_122_ = stack[2].m_obj;
lean_object* v_k_123_ = stack[3].m_obj;
uint8_t v_kind_124_ = stack[4].m_num;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v___y_127_ = stack[7].m_obj;
lean_object* v___y_128_ = stack[8].m_obj;
lean_object* v_res_148_;
v_res_148_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_120_, v_bi_121_, v_type_122_, v_k_123_, v_kind_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg___boxed(lean_object* v_name_149_, lean_object* v_bi_150_, lean_object* v_type_151_, lean_object* v_k_152_, lean_object* v_kind_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
uint8_t v_bi_boxed_159_; uint8_t v_kind_boxed_160_; lean_object* v_res_161_; 
v_bi_boxed_159_ = lean_unbox(v_bi_150_);
v_kind_boxed_160_ = lean_unbox(v_kind_153_);
v_res_161_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_149_, v_bi_boxed_159_, v_type_151_, v_k_152_, v_kind_boxed_160_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_161_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(lean_object* v_name_162_, lean_object* v_type_163_, lean_object* v_k_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; 
v___x_170_ = 0;
v___x_171_ = 0;
v___x_172_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_162_, v___x_170_, v_type_163_, v_k_164_, v___x_171_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
return v___x_172_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_162_ = stack[0].m_obj;
lean_object* v_type_163_ = stack[1].m_obj;
lean_object* v_k_164_ = stack[2].m_obj;
lean_object* v___y_165_ = stack[3].m_obj;
lean_object* v___y_166_ = stack[4].m_obj;
lean_object* v___y_167_ = stack[5].m_obj;
lean_object* v___y_168_ = stack[6].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_162_, v_type_163_, v_k_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg___boxed(lean_object* v_name_174_, lean_object* v_type_175_, lean_object* v_k_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_174_, v_type_175_, v_k_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(lean_object* v_xs_189_, lean_object* v___x_190_, uint8_t v___x_191_, uint8_t v___x_192_, uint8_t v___x_193_, lean_object* v_f_194_, lean_object* v_g_195_, lean_object* v_a_196_, lean_object* v___x_197_, lean_object* v_a_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_00_u03b2_203_, lean_object* v_h_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_mkForallFVars(v_xs_189_, v___x_190_, v___x_191_, v___x_192_, v___x_192_, v___x_193_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = lean_unsigned_to_nat(2u);
v___x_213_ = lean_mk_empty_array_with_capacity(v___x_212_);
lean_inc_ref(v_f_194_);
v___x_214_ = lean_array_push(v___x_213_, v_f_194_);
lean_inc_ref(v_g_195_);
v___x_215_ = lean_array_push(v___x_214_, v_g_195_);
v___x_216_ = l_Lean_Meta_mkLambdaFVars(v___x_215_, v_a_211_, v___x_191_, v___x_192_, v___x_191_, v___x_192_, v___x_193_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec_ref(v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_n(v_a_217_, 2);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__0));
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__1));
lean_inc(v_a_196_);
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v_a_196_);
lean_ctor_set(v___x_220_, 1, v___x_197_);
lean_inc_ref(v___x_220_);
v___x_221_ = l_Lean_mkConst(v___x_219_, v___x_220_);
lean_inc_ref(v_a_198_);
v___x_222_ = l_Lean_mkAppB(v___x_221_, v_a_198_, v_a_217_);
v___x_223_ = lean_box(v___x_191_);
v___x_224_ = lean_box(v___x_192_);
v___x_225_ = lean_box(v___x_193_);
lean_inc_ref(v___x_222_);
v___f_226_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__0___boxed), 24, 18);
lean_closure_set(v___f_226_, 0, v___x_218_);
lean_closure_set(v___f_226_, 1, v_a_196_);
lean_closure_set(v___f_226_, 2, v___x_199_);
lean_closure_set(v___f_226_, 3, v_xs_189_);
lean_closure_set(v___f_226_, 4, v___x_200_);
lean_closure_set(v___f_226_, 5, v_a_198_);
lean_closure_set(v___f_226_, 6, v_a_217_);
lean_closure_set(v___f_226_, 7, v___x_201_);
lean_closure_set(v___f_226_, 8, v___x_202_);
lean_closure_set(v___f_226_, 9, v_00_u03b2_203_);
lean_closure_set(v___f_226_, 10, v___x_223_);
lean_closure_set(v___f_226_, 11, v___x_224_);
lean_closure_set(v___f_226_, 12, v___x_225_);
lean_closure_set(v___f_226_, 13, v___x_220_);
lean_closure_set(v___f_226_, 14, v_f_194_);
lean_closure_set(v___f_226_, 15, v_g_195_);
lean_closure_set(v___f_226_, 16, v_h_204_);
lean_closure_set(v___f_226_, 17, v___x_222_);
v___x_227_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___closed__3));
v___x_228_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_227_, v___x_222_, v___f_226_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v___x_228_;
}
else
{
lean_dec_ref(v_h_204_);
lean_dec_ref(v_00_u03b2_203_);
lean_dec(v___x_202_);
lean_dec(v___x_201_);
lean_dec(v___x_200_);
lean_dec(v___x_199_);
lean_dec_ref(v_a_198_);
lean_dec(v___x_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_g_195_);
lean_dec_ref(v_f_194_);
lean_dec_ref(v_xs_189_);
return v___x_216_;
}
}
else
{
lean_dec_ref(v_h_204_);
lean_dec_ref(v_00_u03b2_203_);
lean_dec(v___x_202_);
lean_dec(v___x_201_);
lean_dec(v___x_200_);
lean_dec(v___x_199_);
lean_dec_ref(v_a_198_);
lean_dec(v___x_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_g_195_);
lean_dec_ref(v_f_194_);
lean_dec_ref(v_xs_189_);
return v___x_210_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_189_ = stack[0].m_obj;
lean_object* v___x_190_ = stack[1].m_obj;
uint8_t v___x_191_ = stack[2].m_num;
uint8_t v___x_192_ = stack[3].m_num;
uint8_t v___x_193_ = stack[4].m_num;
lean_object* v_f_194_ = stack[5].m_obj;
lean_object* v_g_195_ = stack[6].m_obj;
lean_object* v_a_196_ = stack[7].m_obj;
lean_object* v___x_197_ = stack[8].m_obj;
lean_object* v_a_198_ = stack[9].m_obj;
lean_object* v___x_199_ = stack[10].m_obj;
lean_object* v___x_200_ = stack[11].m_obj;
lean_object* v___x_201_ = stack[12].m_obj;
lean_object* v___x_202_ = stack[13].m_obj;
lean_object* v_00_u03b2_203_ = stack[14].m_obj;
lean_object* v_h_204_ = stack[15].m_obj;
lean_object* v___y_205_ = stack[16].m_obj;
lean_object* v___y_206_ = stack[17].m_obj;
lean_object* v___y_207_ = stack[18].m_obj;
lean_object* v___y_208_ = stack[19].m_obj;
lean_object* v_res_229_;
v_res_229_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(v_xs_189_, v___x_190_, v___x_191_, v___x_192_, v___x_193_, v_f_194_, v_g_195_, v_a_196_, v___x_197_, v_a_198_, v___x_199_, v___x_200_, v___x_201_, v___x_202_, v_00_u03b2_203_, v_h_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed(lean_object** _args){
lean_object* v_xs_230_ = _args[0];
lean_object* v___x_231_ = _args[1];
lean_object* v___x_232_ = _args[2];
lean_object* v___x_233_ = _args[3];
lean_object* v___x_234_ = _args[4];
lean_object* v_f_235_ = _args[5];
lean_object* v_g_236_ = _args[6];
lean_object* v_a_237_ = _args[7];
lean_object* v___x_238_ = _args[8];
lean_object* v_a_239_ = _args[9];
lean_object* v___x_240_ = _args[10];
lean_object* v___x_241_ = _args[11];
lean_object* v___x_242_ = _args[12];
lean_object* v___x_243_ = _args[13];
lean_object* v_00_u03b2_244_ = _args[14];
lean_object* v_h_245_ = _args[15];
lean_object* v___y_246_ = _args[16];
lean_object* v___y_247_ = _args[17];
lean_object* v___y_248_ = _args[18];
lean_object* v___y_249_ = _args[19];
lean_object* v___y_250_ = _args[20];
_start:
{
uint8_t v___x_2333__boxed_251_; uint8_t v___x_2334__boxed_252_; uint8_t v___x_2335__boxed_253_; lean_object* v_res_254_; 
v___x_2333__boxed_251_ = lean_unbox(v___x_232_);
v___x_2334__boxed_252_ = lean_unbox(v___x_233_);
v___x_2335__boxed_253_ = lean_unbox(v___x_234_);
v_res_254_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1(v_xs_230_, v___x_231_, v___x_2333__boxed_251_, v___x_2334__boxed_252_, v___x_2335__boxed_253_, v_f_235_, v_g_236_, v_a_237_, v___x_238_, v_a_239_, v___x_240_, v___x_241_, v___x_242_, v___x_243_, v_00_u03b2_244_, v_h_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_254_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(lean_object* v_a_261_, lean_object* v_f_262_, lean_object* v_xs_263_, lean_object* v_00_u03b2_264_, uint8_t v___x_265_, uint8_t v___x_266_, uint8_t v___x_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v___x_270_, lean_object* v___x_271_, lean_object* v_g_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__1));
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v_a_261_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
lean_inc_ref(v___x_280_);
v___x_281_ = l_Lean_mkConst(v___x_278_, v___x_280_);
lean_inc_ref(v_f_262_);
v___x_282_ = l_Lean_mkAppN(v_f_262_, v_xs_263_);
lean_inc_ref(v_g_272_);
v___x_283_ = l_Lean_mkAppN(v_g_272_, v_xs_263_);
lean_inc_ref(v_00_u03b2_264_);
v___x_284_ = l_Lean_mkApp3(v___x_281_, v_00_u03b2_264_, v___x_282_, v___x_283_);
lean_inc_ref(v___x_284_);
v___x_285_ = l_Lean_Meta_mkForallFVars(v_xs_263_, v___x_284_, v___x_265_, v___x_266_, v___x_266_, v___x_267_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___f_291_; lean_object* v___x_292_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___closed__3));
v___x_288_ = lean_box(v___x_265_);
v___x_289_ = lean_box(v___x_266_);
v___x_290_ = lean_box(v___x_267_);
v___f_291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__1___boxed), 21, 15);
lean_closure_set(v___f_291_, 0, v_xs_263_);
lean_closure_set(v___f_291_, 1, v___x_284_);
lean_closure_set(v___f_291_, 2, v___x_288_);
lean_closure_set(v___f_291_, 3, v___x_289_);
lean_closure_set(v___f_291_, 4, v___x_290_);
lean_closure_set(v___f_291_, 5, v_f_262_);
lean_closure_set(v___f_291_, 6, v_g_272_);
lean_closure_set(v___f_291_, 7, v_a_268_);
lean_closure_set(v___f_291_, 8, v___x_279_);
lean_closure_set(v___f_291_, 9, v_a_269_);
lean_closure_set(v___f_291_, 10, v___x_280_);
lean_closure_set(v___f_291_, 11, v___x_270_);
lean_closure_set(v___f_291_, 12, v___x_287_);
lean_closure_set(v___f_291_, 13, v___x_271_);
lean_closure_set(v___f_291_, 14, v_00_u03b2_264_);
v___x_292_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_287_, v_a_286_, v___f_291_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
return v___x_292_;
}
else
{
lean_dec_ref(v___x_284_);
lean_dec_ref_known(v___x_280_, 2);
lean_dec_ref(v_g_272_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_00_u03b2_264_);
lean_dec_ref(v_xs_263_);
lean_dec_ref(v_f_262_);
return v___x_285_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_261_ = stack[0].m_obj;
lean_object* v_f_262_ = stack[1].m_obj;
lean_object* v_xs_263_ = stack[2].m_obj;
lean_object* v_00_u03b2_264_ = stack[3].m_obj;
uint8_t v___x_265_ = stack[4].m_num;
uint8_t v___x_266_ = stack[5].m_num;
uint8_t v___x_267_ = stack[6].m_num;
lean_object* v_a_268_ = stack[7].m_obj;
lean_object* v_a_269_ = stack[8].m_obj;
lean_object* v___x_270_ = stack[9].m_obj;
lean_object* v___x_271_ = stack[10].m_obj;
lean_object* v_g_272_ = stack[11].m_obj;
lean_object* v___y_273_ = stack[12].m_obj;
lean_object* v___y_274_ = stack[13].m_obj;
lean_object* v___y_275_ = stack[14].m_obj;
lean_object* v___y_276_ = stack[15].m_obj;
lean_object* v_res_293_;
v_res_293_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(v_a_261_, v_f_262_, v_xs_263_, v_00_u03b2_264_, v___x_265_, v___x_266_, v___x_267_, v_a_268_, v_a_269_, v___x_270_, v___x_271_, v_g_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed(lean_object** _args){
lean_object* v_a_294_ = _args[0];
lean_object* v_f_295_ = _args[1];
lean_object* v_xs_296_ = _args[2];
lean_object* v_00_u03b2_297_ = _args[3];
lean_object* v___x_298_ = _args[4];
lean_object* v___x_299_ = _args[5];
lean_object* v___x_300_ = _args[6];
lean_object* v_a_301_ = _args[7];
lean_object* v_a_302_ = _args[8];
lean_object* v___x_303_ = _args[9];
lean_object* v___x_304_ = _args[10];
lean_object* v_g_305_ = _args[11];
lean_object* v___y_306_ = _args[12];
lean_object* v___y_307_ = _args[13];
lean_object* v___y_308_ = _args[14];
lean_object* v___y_309_ = _args[15];
lean_object* v___y_310_ = _args[16];
_start:
{
uint8_t v___x_2496__boxed_311_; uint8_t v___x_2497__boxed_312_; uint8_t v___x_2498__boxed_313_; lean_object* v_res_314_; 
v___x_2496__boxed_311_ = lean_unbox(v___x_298_);
v___x_2497__boxed_312_ = lean_unbox(v___x_299_);
v___x_2498__boxed_313_ = lean_unbox(v___x_300_);
v_res_314_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2(v_a_294_, v_f_295_, v_xs_296_, v_00_u03b2_297_, v___x_2496__boxed_311_, v___x_2497__boxed_312_, v___x_2498__boxed_313_, v_a_301_, v_a_302_, v___x_303_, v___x_304_, v_g_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_314_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(lean_object* v_a_318_, lean_object* v_xs_319_, lean_object* v_00_u03b2_320_, uint8_t v___x_321_, uint8_t v___x_322_, uint8_t v___x_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v___x_326_, lean_object* v_f_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___closed__1));
v___x_334_ = lean_box(v___x_321_);
v___x_335_ = lean_box(v___x_322_);
v___x_336_ = lean_box(v___x_323_);
lean_inc_ref(v_a_325_);
v___f_337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__2___boxed), 17, 11);
lean_closure_set(v___f_337_, 0, v_a_318_);
lean_closure_set(v___f_337_, 1, v_f_327_);
lean_closure_set(v___f_337_, 2, v_xs_319_);
lean_closure_set(v___f_337_, 3, v_00_u03b2_320_);
lean_closure_set(v___f_337_, 4, v___x_334_);
lean_closure_set(v___f_337_, 5, v___x_335_);
lean_closure_set(v___f_337_, 6, v___x_336_);
lean_closure_set(v___f_337_, 7, v_a_324_);
lean_closure_set(v___f_337_, 8, v_a_325_);
lean_closure_set(v___f_337_, 9, v___x_326_);
lean_closure_set(v___f_337_, 10, v___x_333_);
v___x_338_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_333_, v_a_325_, v___f_337_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v___x_338_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_318_ = stack[0].m_obj;
lean_object* v_xs_319_ = stack[1].m_obj;
lean_object* v_00_u03b2_320_ = stack[2].m_obj;
uint8_t v___x_321_ = stack[3].m_num;
uint8_t v___x_322_ = stack[4].m_num;
uint8_t v___x_323_ = stack[5].m_num;
lean_object* v_a_324_ = stack[6].m_obj;
lean_object* v_a_325_ = stack[7].m_obj;
lean_object* v___x_326_ = stack[8].m_obj;
lean_object* v_f_327_ = stack[9].m_obj;
lean_object* v___y_328_ = stack[10].m_obj;
lean_object* v___y_329_ = stack[11].m_obj;
lean_object* v___y_330_ = stack[12].m_obj;
lean_object* v___y_331_ = stack[13].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(v_a_318_, v_xs_319_, v_00_u03b2_320_, v___x_321_, v___x_322_, v___x_323_, v_a_324_, v_a_325_, v___x_326_, v_f_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed(lean_object* v_a_340_, lean_object* v_xs_341_, lean_object* v_00_u03b2_342_, lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v___x_348_, lean_object* v_f_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_2625__boxed_355_; uint8_t v___x_2626__boxed_356_; uint8_t v___x_2627__boxed_357_; lean_object* v_res_358_; 
v___x_2625__boxed_355_ = lean_unbox(v___x_343_);
v___x_2626__boxed_356_ = lean_unbox(v___x_344_);
v___x_2627__boxed_357_ = lean_unbox(v___x_345_);
v_res_358_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3(v_a_340_, v_xs_341_, v_00_u03b2_342_, v___x_2625__boxed_355_, v___x_2626__boxed_356_, v___x_2627__boxed_357_, v_a_346_, v_a_347_, v___x_348_, v_f_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_358_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(lean_object* v_xs_362_, lean_object* v_00_u03b2_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
uint8_t v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
v___x_369_ = 0;
v___x_370_ = 1;
v___x_371_ = 1;
lean_inc_ref(v_00_u03b2_363_);
v___x_372_ = l_Lean_Meta_mkForallFVars(v_xs_362_, v_00_u03b2_363_, v___x_369_, v___x_370_, v___x_370_, v___x_371_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
lean_inc_ref(v_00_u03b2_363_);
v___x_374_ = l_Lean_Meta_getLevel(v_00_u03b2_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
lean_inc(v_a_373_);
v___x_376_ = l_Lean_Meta_getLevel(v_a_373_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___x_383_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___closed__1));
v___x_379_ = lean_box(v___x_369_);
v___x_380_ = lean_box(v___x_370_);
v___x_381_ = lean_box(v___x_371_);
lean_inc(v_a_373_);
v___f_382_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___lam__3___boxed), 15, 9);
lean_closure_set(v___f_382_, 0, v_a_375_);
lean_closure_set(v___f_382_, 1, v_xs_362_);
lean_closure_set(v___f_382_, 2, v_00_u03b2_363_);
lean_closure_set(v___f_382_, 3, v___x_379_);
lean_closure_set(v___f_382_, 4, v___x_380_);
lean_closure_set(v___f_382_, 5, v___x_381_);
lean_closure_set(v___f_382_, 6, v_a_377_);
lean_closure_set(v___f_382_, 7, v_a_373_);
lean_closure_set(v___f_382_, 8, v___x_378_);
v___x_383_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v___x_378_, v_a_373_, v___f_382_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_383_;
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_dec_ref(v_00_u03b2_363_);
lean_dec_ref(v_xs_362_);
v_a_384_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_376_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_376_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_a_373_);
lean_dec_ref(v_00_u03b2_363_);
lean_dec_ref(v_xs_362_);
v_a_392_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_374_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_374_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b2_363_);
lean_dec_ref(v_xs_362_);
return v___x_372_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_362_ = stack[0].m_obj;
lean_object* v_00_u03b2_363_ = stack[1].m_obj;
lean_object* v_a_364_ = stack[2].m_obj;
lean_object* v_a_365_ = stack[3].m_obj;
lean_object* v_a_366_ = stack[4].m_obj;
lean_object* v_a_367_ = stack[5].m_obj;
lean_object* v_res_400_;
v_res_400_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_362_, v_00_u03b2_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor___boxed(lean_object* v_xs_401_, lean_object* v_00_u03b2_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_401_, v_00_u03b2_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_408_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(lean_object* v_00_u03b1_409_, lean_object* v_name_410_, uint8_t v_bi_411_, lean_object* v_type_412_, lean_object* v_k_413_, uint8_t v_kind_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___redArg(v_name_410_, v_bi_411_, v_type_412_, v_k_413_, v_kind_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_410_ = stack[1].m_obj;
uint8_t v_bi_411_ = stack[2].m_num;
lean_object* v_type_412_ = stack[3].m_obj;
lean_object* v_k_413_ = stack[4].m_obj;
uint8_t v_kind_414_ = stack[5].m_num;
lean_object* v___y_415_ = stack[6].m_obj;
lean_object* v___y_416_ = stack[7].m_obj;
lean_object* v___y_417_ = stack[8].m_obj;
lean_object* v___y_418_ = stack[9].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(lean_box(0), v_name_410_, v_bi_411_, v_type_412_, v_k_413_, v_kind_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_422_, lean_object* v_name_423_, lean_object* v_bi_424_, lean_object* v_type_425_, lean_object* v_k_426_, lean_object* v_kind_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v_bi_boxed_433_; uint8_t v_kind_boxed_434_; lean_object* v_res_435_; 
v_bi_boxed_433_ = lean_unbox(v_bi_424_);
v_kind_boxed_434_ = lean_unbox(v_kind_427_);
v_res_435_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_spec__0(v_00_u03b1_422_, v_name_423_, v_bi_boxed_433_, v_type_425_, v_k_426_, v_kind_boxed_434_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_435_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(lean_object* v_00_u03b1_436_, lean_object* v_name_437_, lean_object* v_type_438_, lean_object* v_k_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___redArg(v_name_437_, v_type_438_, v_k_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_437_ = stack[1].m_obj;
lean_object* v_type_438_ = stack[2].m_obj;
lean_object* v_k_439_ = stack[3].m_obj;
lean_object* v___y_440_ = stack[4].m_obj;
lean_object* v___y_441_ = stack[5].m_obj;
lean_object* v___y_442_ = stack[6].m_obj;
lean_object* v___y_443_ = stack[7].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(lean_box(0), v_name_437_, v_type_438_, v_k_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0___boxed(lean_object* v_00_u03b1_447_, lean_object* v_name_448_, lean_object* v_type_449_, lean_object* v_k_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor_spec__0(v_00_u03b1_447_, v_name_448_, v_type_449_, v_k_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_457_, lean_object* v_vals_458_, lean_object* v_i_459_, lean_object* v_k_460_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_array_get_size(v_keys_457_);
v___x_462_ = lean_nat_dec_lt(v_i_459_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_i_459_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v_k_x27_464_; size_t v___x_465_; size_t v___x_466_; uint8_t v___x_467_; 
v_k_x27_464_ = lean_array_fget_borrowed(v_keys_457_, v_i_459_);
v___x_465_ = lean_ptr_addr(v_k_460_);
v___x_466_ = lean_ptr_addr(v_k_x27_464_);
v___x_467_ = lean_usize_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_i_459_, v___x_468_);
lean_dec(v_i_459_);
v_i_459_ = v___x_469_;
goto _start;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_array_fget_borrowed(v_vals_458_, v_i_459_);
lean_dec(v_i_459_);
lean_inc(v___x_471_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_i_475_, lean_object* v_k_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_473_, v_vals_474_, v_i_475_, v_k_476_);
lean_dec_ref(v_k_476_);
lean_dec_ref(v_vals_474_);
lean_dec_ref(v_keys_473_);
return v_res_477_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(lean_object* v_x_478_, size_t v_x_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v_es_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v_j_485_; lean_object* v___x_486_; 
v_es_481_ = lean_ctor_get(v_x_478_, 0);
v___x_482_ = lean_box(2);
v___x_483_ = ((size_t)31ULL);
v___x_484_ = lean_usize_land(v_x_479_, v___x_483_);
v_j_485_ = lean_usize_to_nat(v___x_484_);
v___x_486_ = lean_array_get_borrowed(v___x_482_, v_es_481_, v_j_485_);
lean_dec(v_j_485_);
switch(lean_obj_tag(v___x_486_))
{
case 0:
{
lean_object* v_key_487_; lean_object* v_val_488_; size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v_key_487_ = lean_ctor_get(v___x_486_, 0);
v_val_488_ = lean_ctor_get(v___x_486_, 1);
v___x_489_ = lean_ptr_addr(v_x_480_);
v___x_490_ = lean_ptr_addr(v_key_487_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
else
{
lean_object* v___x_493_; 
lean_inc(v_val_488_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_val_488_);
return v___x_493_;
}
}
case 1:
{
lean_object* v_node_494_; size_t v___x_495_; size_t v___x_496_; 
v_node_494_ = lean_ctor_get(v___x_486_, 0);
v___x_495_ = ((size_t)5ULL);
v___x_496_ = lean_usize_shift_right(v_x_479_, v___x_495_);
v_x_478_ = v_node_494_;
v_x_479_ = v___x_496_;
goto _start;
}
default: 
{
lean_object* v___x_498_; 
v___x_498_ = lean_box(0);
return v___x_498_;
}
}
}
else
{
lean_object* v_ks_499_; lean_object* v_vs_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_ks_499_ = lean_ctor_get(v_x_478_, 0);
v_vs_500_ = lean_ctor_get(v_x_478_, 1);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_ks_499_, v_vs_500_, v___x_501_, v_x_480_);
return v___x_502_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_478_ = stack[0].m_obj;
size_t v_x_479_ = stack[1].m_num;
lean_object* v_x_480_ = stack[2].m_obj;
lean_object* v_res_503_;
v_res_503_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_478_, v_x_479_, v_x_480_);
stack->m_obj
 = v_res_503_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg___boxed(lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
size_t v_x_7115__boxed_507_; lean_object* v_res_508_; 
v_x_7115__boxed_507_ = lean_unbox_usize(v_x_505_);
lean_dec(v_x_505_);
v_res_508_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_504_, v_x_7115__boxed_507_, v_x_506_);
lean_dec_ref(v_x_506_);
lean_dec_ref(v_x_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; uint64_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_511_ = lean_ptr_addr(v_x_510_);
v___x_512_ = ((size_t)3ULL);
v___x_513_ = lean_usize_shift_right(v___x_511_, v___x_512_);
v___x_514_ = lean_usize_to_uint64(v___x_513_);
v___x_515_ = lean_uint64_to_usize(v___x_514_);
v___x_516_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_509_, v___x_515_, v_x_510_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg___boxed(lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_517_, v_x_518_);
lean_dec_ref(v_x_518_);
lean_dec_ref(v_x_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_ks_524_; lean_object* v_vs_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_551_; 
v_ks_524_ = lean_ctor_get(v_x_520_, 0);
v_vs_525_ = lean_ctor_get(v_x_520_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_551_ == 0)
{
v___x_527_ = v_x_520_;
v_isShared_528_ = v_isSharedCheck_551_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_vs_525_);
lean_inc(v_ks_524_);
lean_dec(v_x_520_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_551_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_get_size(v_ks_524_);
v___x_530_ = lean_nat_dec_lt(v_x_521_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec(v_x_521_);
v___x_531_ = lean_array_push(v_ks_524_, v_x_522_);
v___x_532_ = lean_array_push(v_vs_525_, v_x_523_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_532_);
lean_ctor_set(v___x_527_, 0, v___x_531_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v_k_x27_536_; size_t v___x_537_; size_t v___x_538_; uint8_t v___x_539_; 
v_k_x27_536_ = lean_array_fget_borrowed(v_ks_524_, v_x_521_);
v___x_537_ = lean_ptr_addr(v_x_522_);
v___x_538_ = lean_ptr_addr(v_k_x27_536_);
v___x_539_ = lean_usize_dec_eq(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_541_; 
if (v_isShared_528_ == 0)
{
v___x_541_ = v___x_527_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_ks_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_vs_525_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_x_521_, v___x_542_);
lean_dec(v_x_521_);
v_x_520_ = v___x_541_;
v_x_521_ = v___x_543_;
goto _start;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_array_fset(v_ks_524_, v_x_521_, v_x_522_);
v___x_547_ = lean_array_fset(v_vs_525_, v_x_521_, v_x_523_);
lean_dec(v_x_521_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v___x_547_);
lean_ctor_set(v___x_527_, 0, v___x_546_);
v___x_549_ = v___x_527_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(lean_object* v_n_552_, lean_object* v_k_553_, lean_object* v_v_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_n_552_, v___x_555_, v_k_553_, v_v_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_557_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(lean_object* v_x_558_, size_t v_x_559_, size_t v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v_es_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v_j_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_es_563_ = lean_ctor_get(v_x_558_, 0);
v___x_564_ = ((size_t)31ULL);
v___x_565_ = lean_usize_land(v_x_559_, v___x_564_);
v_j_566_ = lean_usize_to_nat(v___x_565_);
v___x_567_ = lean_array_get_size(v_es_563_);
v___x_568_ = lean_nat_dec_lt(v_j_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v_j_566_);
lean_dec(v_x_562_);
lean_dec_ref(v_x_561_);
return v_x_558_;
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_609_; 
lean_inc_ref(v_es_563_);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v_x_558_, 0);
lean_dec(v_unused_610_);
v___x_570_ = v_x_558_;
v_isShared_571_ = v_isSharedCheck_609_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_x_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_609_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_v_572_; lean_object* v___x_573_; lean_object* v_xs_x27_574_; lean_object* v___y_576_; 
v_v_572_ = lean_array_fget(v_es_563_, v_j_566_);
v___x_573_ = lean_box(0);
v_xs_x27_574_ = lean_array_fset(v_es_563_, v_j_566_, v___x_573_);
switch(lean_obj_tag(v_v_572_))
{
case 0:
{
lean_object* v_key_581_; lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_594_; 
v_key_581_ = lean_ctor_get(v_v_572_, 0);
v_val_582_ = lean_ctor_get(v_v_572_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_v_572_);
if (v_isSharedCheck_594_ == 0)
{
v___x_584_ = v_v_572_;
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_inc(v_key_581_);
lean_dec(v_v_572_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
size_t v___x_586_; size_t v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_ptr_addr(v_x_561_);
v___x_587_ = lean_ptr_addr(v_key_581_);
v___x_588_ = lean_usize_dec_eq(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_del_object(v___x_584_);
v___x_589_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_581_, v_val_582_, v_x_561_, v_x_562_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
v___y_576_ = v___x_590_;
goto v___jp_575_;
}
else
{
lean_object* v___x_592_; 
lean_dec(v_val_582_);
lean_dec(v_key_581_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_x_562_);
lean_ctor_set(v___x_584_, 0, v_x_561_);
v___x_592_ = v___x_584_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_x_561_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_x_562_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v___y_576_ = v___x_592_;
goto v___jp_575_;
}
}
}
}
case 1:
{
lean_object* v_node_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_607_; 
v_node_595_ = lean_ctor_get(v_v_572_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_v_572_);
if (v_isSharedCheck_607_ == 0)
{
v___x_597_ = v_v_572_;
v_isShared_598_ = v_isSharedCheck_607_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_node_595_);
lean_dec(v_v_572_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_607_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_599_ = ((size_t)5ULL);
v___x_600_ = lean_usize_shift_right(v_x_559_, v___x_599_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_add(v_x_560_, v___x_601_);
v___x_603_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_node_595_, v___x_600_, v___x_602_, v_x_561_, v_x_562_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_603_);
v___x_605_ = v___x_597_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v___y_576_ = v___x_605_;
goto v___jp_575_;
}
}
}
default: 
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v_x_561_);
lean_ctor_set(v___x_608_, 1, v_x_562_);
v___y_576_ = v___x_608_;
goto v___jp_575_;
}
}
v___jp_575_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = lean_array_fset(v_xs_x27_574_, v_j_566_, v___y_576_);
lean_dec(v_j_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_577_);
v___x_579_ = v___x_570_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
else
{
lean_object* v_ks_611_; lean_object* v_vs_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_630_; 
v_ks_611_ = lean_ctor_get(v_x_558_, 0);
v_vs_612_ = lean_ctor_get(v_x_558_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_630_ == 0)
{
v___x_614_ = v_x_558_;
v_isShared_615_ = v_isSharedCheck_630_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_vs_612_);
lean_inc(v_ks_611_);
lean_dec(v_x_558_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_630_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_ks_611_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_vs_612_);
v___x_617_ = v_reuseFailAlloc_629_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v_newNode_618_; size_t v___x_619_; uint8_t v___x_620_; 
v_newNode_618_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v___x_617_, v_x_561_, v_x_562_);
v___x_619_ = ((size_t)7ULL);
v___x_620_ = lean_usize_dec_le(v___x_619_, v_x_560_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_618_);
v___x_622_ = lean_unsigned_to_nat(4u);
v___x_623_ = lean_nat_dec_lt(v___x_621_, v___x_622_);
lean_dec(v___x_621_);
if (v___x_623_ == 0)
{
lean_object* v_ks_624_; lean_object* v_vs_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_ks_624_ = lean_ctor_get(v_newNode_618_, 0);
lean_inc_ref(v_ks_624_);
v_vs_625_ = lean_ctor_get(v_newNode_618_, 1);
lean_inc_ref(v_vs_625_);
lean_dec_ref(v_newNode_618_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___closed__0);
v___x_628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_x_560_, v_ks_624_, v_vs_625_, v___x_626_, v___x_627_);
lean_dec_ref(v_vs_625_);
lean_dec_ref(v_ks_624_);
return v___x_628_;
}
else
{
return v_newNode_618_;
}
}
else
{
return v_newNode_618_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_558_ = stack[0].m_obj;
size_t v_x_559_ = stack[1].m_num;
size_t v_x_560_ = stack[2].m_num;
lean_object* v_x_561_ = stack[3].m_obj;
lean_object* v_x_562_ = stack[4].m_obj;
lean_object* v_res_631_;
v_res_631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_558_, v_x_559_, v_x_560_, v_x_561_, v_x_562_);
stack->m_obj
 = v_res_631_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(size_t v_depth_632_, lean_object* v_keys_633_, lean_object* v_vals_634_, lean_object* v_i_635_, lean_object* v_entries_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_keys_633_);
v___x_638_ = lean_nat_dec_lt(v_i_635_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec(v_i_635_);
return v_entries_636_;
}
else
{
lean_object* v_k_639_; lean_object* v_v_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; uint64_t v___x_644_; size_t v_h_645_; size_t v___x_646_; lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v_h_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_k_639_ = lean_array_fget_borrowed(v_keys_633_, v_i_635_);
v_v_640_ = lean_array_fget_borrowed(v_vals_634_, v_i_635_);
v___x_641_ = lean_ptr_addr(v_k_639_);
v___x_642_ = ((size_t)3ULL);
v___x_643_ = lean_usize_shift_right(v___x_641_, v___x_642_);
v___x_644_ = lean_usize_to_uint64(v___x_643_);
v_h_645_ = lean_uint64_to_usize(v___x_644_);
v___x_646_ = ((size_t)5ULL);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_sub(v_depth_632_, v___x_648_);
v___x_650_ = lean_usize_mul(v___x_646_, v___x_649_);
v_h_651_ = lean_usize_shift_right(v_h_645_, v___x_650_);
v___x_652_ = lean_nat_add(v_i_635_, v___x_647_);
lean_dec(v_i_635_);
lean_inc(v_v_640_);
lean_inc(v_k_639_);
v___x_653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_entries_636_, v_h_651_, v_depth_632_, v_k_639_, v_v_640_);
v_i_635_ = v___x_652_;
v_entries_636_ = v___x_653_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_632_ = stack[0].m_num;
lean_object* v_keys_633_ = stack[1].m_obj;
lean_object* v_vals_634_ = stack[2].m_obj;
lean_object* v_i_635_ = stack[3].m_obj;
lean_object* v_entries_636_ = stack[4].m_obj;
lean_object* v_res_655_;
v_res_655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_632_, v_keys_633_, v_vals_634_, v_i_635_, v_entries_636_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_656_, lean_object* v_keys_657_, lean_object* v_vals_658_, lean_object* v_i_659_, lean_object* v_entries_660_){
_start:
{
size_t v_depth_boxed_661_; lean_object* v_res_662_; 
v_depth_boxed_661_ = lean_unbox_usize(v_depth_656_);
lean_dec(v_depth_656_);
v_res_662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_boxed_661_, v_keys_657_, v_vals_658_, v_i_659_, v_entries_660_);
lean_dec_ref(v_vals_658_);
lean_dec_ref(v_keys_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg___boxed(lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
size_t v_x_7337__boxed_668_; size_t v_x_7338__boxed_669_; lean_object* v_res_670_; 
v_x_7337__boxed_668_ = lean_unbox_usize(v_x_664_);
lean_dec(v_x_664_);
v_x_7338__boxed_669_ = lean_unbox_usize(v_x_665_);
lean_dec(v_x_665_);
v_res_670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_663_, v_x_7337__boxed_668_, v_x_7338__boxed_669_, v_x_666_, v_x_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
size_t v___x_674_; size_t v___x_675_; size_t v___x_676_; uint64_t v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v___x_674_ = lean_ptr_addr(v_x_672_);
v___x_675_ = ((size_t)3ULL);
v___x_676_ = lean_usize_shift_right(v___x_674_, v___x_675_);
v___x_677_ = lean_usize_to_uint64(v___x_676_);
v___x_678_ = lean_uint64_to_usize(v___x_677_);
v___x_679_ = ((size_t)1ULL);
v___x_680_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_671_, v___x_678_, v___x_679_, v_x_672_, v_x_673_);
return v___x_680_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(lean_object* v_e_681_, lean_object* v_xs_682_, lean_object* v_b_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
lean_inc(v_a_688_);
lean_inc_ref(v_a_687_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
v___x_690_ = lean_infer_type(v_e_681_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_727_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_727_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_727_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_727_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v_funext_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_get(v_a_684_);
v_funext_696_ = lean_ctor_get(v___x_695_, 3);
lean_inc_ref(v_funext_696_);
lean_dec(v___x_695_);
v___x_697_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_funext_696_, v_a_691_);
lean_dec_ref(v_funext_696_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_val_698_; lean_object* v___x_700_; 
lean_dec(v_a_691_);
lean_dec_ref(v_b_683_);
lean_dec_ref(v_xs_682_);
v_val_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v___x_697_, 1);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_val_698_);
v___x_700_ = v___x_693_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_val_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v___x_702_; 
lean_dec(v___x_697_);
lean_del_object(v___x_693_);
lean_inc(v_a_688_);
lean_inc_ref(v_a_687_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
v___x_702_ = lean_infer_type(v_b_683_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_mkFunextFor(v_xs_682_, v_a_703_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_726_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_726_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_726_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_726_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v_numSteps_710_; lean_object* v_persistentCache_711_; lean_object* v_transientCache_712_; lean_object* v_funext_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_725_; 
v___x_709_ = lean_st_ref_take(v_a_684_);
v_numSteps_710_ = lean_ctor_get(v___x_709_, 0);
v_persistentCache_711_ = lean_ctor_get(v___x_709_, 1);
v_transientCache_712_ = lean_ctor_get(v___x_709_, 2);
v_funext_713_ = lean_ctor_get(v___x_709_, 3);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_715_ = v___x_709_;
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_funext_713_);
lean_inc(v_transientCache_712_);
lean_inc(v_persistentCache_711_);
lean_inc(v_numSteps_710_);
lean_dec(v___x_709_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
lean_inc(v_a_705_);
v___x_717_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_funext_713_, v_a_691_, v_a_705_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 3, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_numSteps_710_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_persistentCache_711_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_transientCache_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v___x_717_);
v___x_719_ = v_reuseFailAlloc_724_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_st_ref_put(v_a_684_, v___x_719_);
if (v_isShared_708_ == 0)
{
v___x_722_ = v___x_707_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_705_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
else
{
lean_dec(v_a_691_);
return v___x_704_;
}
}
else
{
lean_dec(v_a_691_);
lean_dec_ref(v_xs_682_);
return v___x_702_;
}
}
}
}
else
{
lean_dec_ref(v_b_683_);
lean_dec_ref(v_xs_682_);
return v___x_690_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_681_ = stack[0].m_obj;
lean_object* v_xs_682_ = stack[1].m_obj;
lean_object* v_b_683_ = stack[2].m_obj;
lean_object* v_a_684_ = stack[3].m_obj;
lean_object* v_a_685_ = stack[4].m_obj;
lean_object* v_a_686_ = stack[5].m_obj;
lean_object* v_a_687_ = stack[6].m_obj;
lean_object* v_a_688_ = stack[7].m_obj;
lean_object* v_res_728_;
v_res_728_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_681_, v_xs_682_, v_b_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
stack->m_obj
 = v_res_728_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg___boxed(lean_object* v_e_729_, lean_object* v_xs_730_, lean_object* v_b_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_729_, v_xs_730_, v_b_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
return v_res_738_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(lean_object* v_e_739_, lean_object* v_xs_740_, lean_object* v_b_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_739_, v_xs_740_, v_b_741_, v_a_744_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_752_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_739_ = stack[0].m_obj;
lean_object* v_xs_740_ = stack[1].m_obj;
lean_object* v_b_741_ = stack[2].m_obj;
lean_object* v_a_742_ = stack[3].m_obj;
lean_object* v_a_743_ = stack[4].m_obj;
lean_object* v_a_744_ = stack[5].m_obj;
lean_object* v_a_745_ = stack[6].m_obj;
lean_object* v_a_746_ = stack[7].m_obj;
lean_object* v_a_747_ = stack[8].m_obj;
lean_object* v_a_748_ = stack[9].m_obj;
lean_object* v_a_749_ = stack[10].m_obj;
lean_object* v_a_750_ = stack[11].m_obj;
lean_object* v_res_753_;
v_res_753_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(v_e_739_, v_xs_740_, v_b_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___boxed(lean_object* v_e_754_, lean_object* v_xs_755_, lean_object* v_b_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext(v_e_754_, v_xs_755_, v_b_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___redArg(v_x_769_, v_x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0___boxed(lean_object* v_00_u03b2_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0(v_00_u03b2_772_, v_x_773_, v_x_774_);
lean_dec_ref(v_x_774_);
lean_dec_ref(v_x_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1(lean_object* v_00_u03b2_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1___redArg(v_x_777_, v_x_778_, v_x_779_);
return v___x_780_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_object* v_00_u03b2_781_, lean_object* v_x_782_, size_t v_x_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___redArg(v_x_782_, v_x_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_782_ = stack[1].m_obj;
size_t v_x_783_ = stack[2].m_num;
lean_object* v_x_784_ = stack[3].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(lean_box(0), v_x_782_, v_x_783_, v_x_784_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0___boxed(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
size_t v_x_7755__boxed_791_; lean_object* v_res_792_; 
v_x_7755__boxed_791_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_792_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0(v_00_u03b2_787_, v_x_788_, v_x_7755__boxed_791_, v_x_790_);
lean_dec_ref(v_x_790_);
lean_dec_ref(v_x_788_);
return v_res_792_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, size_t v_x_795_, size_t v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___redArg(v_x_794_, v_x_795_, v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_794_ = stack[1].m_obj;
size_t v_x_795_ = stack[2].m_num;
size_t v_x_796_ = stack[3].m_num;
lean_object* v_x_797_ = stack[4].m_obj;
lean_object* v_x_798_ = stack[5].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(lean_box(0), v_x_794_, v_x_795_, v_x_796_, v_x_797_, v_x_798_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2___boxed(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
size_t v_x_7773__boxed_807_; size_t v_x_7774__boxed_808_; lean_object* v_res_809_; 
v_x_7773__boxed_807_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_x_7774__boxed_808_ = lean_unbox_usize(v_x_804_);
lean_dec(v_x_804_);
v_res_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2(v_00_u03b2_801_, v_x_802_, v_x_7773__boxed_807_, v_x_7774__boxed_808_, v_x_805_, v_x_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_810_, lean_object* v_keys_811_, lean_object* v_vals_812_, lean_object* v_heq_813_, lean_object* v_i_814_, lean_object* v_k_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___redArg(v_keys_811_, v_vals_812_, v_i_814_, v_k_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_817_, lean_object* v_keys_818_, lean_object* v_vals_819_, lean_object* v_heq_820_, lean_object* v_i_821_, lean_object* v_k_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__0_spec__0_spec__1(v_00_u03b2_817_, v_keys_818_, v_vals_819_, v_heq_820_, v_i_821_, v_k_822_);
lean_dec_ref(v_k_822_);
lean_dec_ref(v_vals_819_);
lean_dec_ref(v_keys_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_824_, lean_object* v_n_825_, lean_object* v_k_826_, lean_object* v_v_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4___redArg(v_n_825_, v_k_826_, v_v_827_);
return v___x_828_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_829_, size_t v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_heq_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___redArg(v_depth_830_, v_keys_831_, v_vals_832_, v_i_834_, v_entries_835_);
return v___x_836_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_830_ = stack[1].m_num;
lean_object* v_keys_831_ = stack[2].m_obj;
lean_object* v_vals_832_ = stack[3].m_obj;
lean_object* v_i_834_ = stack[5].m_obj;
lean_object* v_entries_835_ = stack[6].m_obj;
lean_object* v_res_837_;
v_res_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(lean_box(0), v_depth_830_, v_keys_831_, v_vals_832_, lean_box(0), v_i_834_, v_entries_835_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_838_, lean_object* v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_heq_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
size_t v_depth_boxed_845_; lean_object* v_res_846_; 
v_depth_boxed_845_ = lean_unbox_usize(v_depth_839_);
lean_dec(v_depth_839_);
v_res_846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__5(v_00_u03b2_838_, v_depth_boxed_845_, v_keys_840_, v_vals_841_, v_heq_842_, v_i_843_, v_entries_844_);
lean_dec_ref(v_vals_841_);
lean_dec_ref(v_keys_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext_spec__1_spec__2_spec__4_spec__5___redArg(v_x_848_, v_x_849_, v_x_850_, v_x_851_);
return v___x_852_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(lean_object* v_simpBody_853_, lean_object* v_e_854_, lean_object* v_xs_855_, lean_object* v_b_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; 
lean_inc(v_a_865_);
lean_inc_ref(v_a_864_);
lean_inc(v_a_863_);
lean_inc_ref(v_a_862_);
lean_inc(v_a_861_);
lean_inc_ref(v_a_860_);
lean_inc(v_a_859_);
lean_inc_ref(v_a_858_);
lean_inc(v_a_857_);
lean_inc_ref(v_b_856_);
v___x_867_ = lean_apply_11(v_simpBody_853_, v_b_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, lean_box(0));
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_938_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_938_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_938_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_938_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
if (lean_obj_tag(v_a_868_) == 0)
{
uint8_t v_contextDependent_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_dec_ref(v_b_856_);
lean_dec_ref(v_xs_855_);
lean_dec_ref(v_e_854_);
v_contextDependent_872_ = lean_ctor_get_uint8(v_a_868_, 1);
lean_dec_ref_known(v_a_868_, 0);
v___x_873_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_872_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_873_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v_e_x27_877_; lean_object* v_proof_878_; uint8_t v_contextDependent_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_870_);
v_e_x27_877_ = lean_ctor_get(v_a_868_, 0);
v_proof_878_ = lean_ctor_get(v_a_868_, 1);
v_contextDependent_879_ = lean_ctor_get_uint8(v_a_868_, sizeof(void*)*2 + 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_937_ == 0)
{
v___x_881_ = v_a_868_;
v_isShared_882_ = v_isSharedCheck_937_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_proof_878_);
lean_inc(v_e_x27_877_);
lean_dec(v_a_868_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_937_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; uint8_t v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v___x_883_ = 0;
v___x_884_ = 1;
v___x_885_ = 1;
v___x_886_ = l_Lean_Meta_mkLambdaFVars(v_xs_855_, v_proof_878_, v___x_883_, v___x_884_, v___x_883_, v___x_884_, v___x_885_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = l_Lean_Meta_mkLambdaFVars(v_xs_855_, v_e_x27_877_, v___x_883_, v___x_884_, v___x_883_, v___x_884_, v___x_885_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Lean_Meta_Sym_shareCommon(v_a_889_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
lean_inc_ref(v_e_854_);
v___x_892_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_getFunext___redArg(v_e_854_, v_xs_855_, v_b_856_, v_a_859_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_904_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_904_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_904_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_904_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_inc(v_a_891_);
v___x_897_ = l_Lean_mkApp3(v_a_893_, v_e_854_, v_a_891_, v_a_887_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_897_);
lean_ctor_set(v___x_881_, 0, v_a_891_);
v___x_899_ = v___x_881_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_891_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_903_, sizeof(void*)*2 + 1, v_contextDependent_879_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*2, v___x_883_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_899_);
v___x_901_ = v___x_895_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_891_);
lean_dec(v_a_887_);
lean_del_object(v___x_881_);
lean_dec_ref(v_e_854_);
v_a_905_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_892_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_892_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_887_);
lean_del_object(v___x_881_);
lean_dec_ref(v_b_856_);
lean_dec_ref(v_xs_855_);
lean_dec_ref(v_e_854_);
v_a_913_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_890_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_890_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_a_887_);
lean_del_object(v___x_881_);
lean_dec_ref(v_b_856_);
lean_dec_ref(v_xs_855_);
lean_dec_ref(v_e_854_);
v_a_921_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_888_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_888_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_881_);
lean_dec_ref(v_e_x27_877_);
lean_dec_ref(v_b_856_);
lean_dec_ref(v_xs_855_);
lean_dec_ref(v_e_854_);
v_a_929_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_886_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_886_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_b_856_);
lean_dec_ref(v_xs_855_);
lean_dec_ref(v_e_854_);
return v___x_867_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_853_ = stack[0].m_obj;
lean_object* v_e_854_ = stack[1].m_obj;
lean_object* v_xs_855_ = stack[2].m_obj;
lean_object* v_b_856_ = stack[3].m_obj;
lean_object* v_a_857_ = stack[4].m_obj;
lean_object* v_a_858_ = stack[5].m_obj;
lean_object* v_a_859_ = stack[6].m_obj;
lean_object* v_a_860_ = stack[7].m_obj;
lean_object* v_a_861_ = stack[8].m_obj;
lean_object* v_a_862_ = stack[9].m_obj;
lean_object* v_a_863_ = stack[10].m_obj;
lean_object* v_a_864_ = stack[11].m_obj;
lean_object* v_a_865_ = stack[12].m_obj;
lean_object* v_res_939_;
v_res_939_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_853_, v_e_854_, v_xs_855_, v_b_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main___boxed(lean_object* v_simpBody_940_, lean_object* v_e_941_, lean_object* v_xs_942_, lean_object* v_b_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_940_, v_e_941_, v_xs_942_, v_b_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
return v_res_954_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(lean_object* v_k_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v_b_961_, lean_object* v_c_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
v___x_968_ = lean_apply_12(v_k_955_, v_b_961_, v_c_962_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, lean_box(0));
return v___x_968_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_955_ = stack[0].m_obj;
lean_object* v___y_956_ = stack[1].m_obj;
lean_object* v___y_957_ = stack[2].m_obj;
lean_object* v___y_958_ = stack[3].m_obj;
lean_object* v___y_959_ = stack[4].m_obj;
lean_object* v___y_960_ = stack[5].m_obj;
lean_object* v_b_961_ = stack[6].m_obj;
lean_object* v_c_962_ = stack[7].m_obj;
lean_object* v___y_963_ = stack[8].m_obj;
lean_object* v___y_964_ = stack[9].m_obj;
lean_object* v___y_965_ = stack[10].m_obj;
lean_object* v___y_966_ = stack[11].m_obj;
lean_object* v_res_969_;
v_res_969_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(v_k_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v_b_961_, v_c_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed(lean_object* v_k_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v_b_976_, lean_object* v_c_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0(v_k_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v_b_976_, v_c_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
return v_res_983_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(lean_object* v_e_984_, lean_object* v_k_985_, uint8_t v_cleanupAnnotations_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___f_997_; uint8_t v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
v___f_997_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_997_, 0, v_k_985_);
lean_closure_set(v___f_997_, 1, v___y_987_);
lean_closure_set(v___f_997_, 2, v___y_988_);
lean_closure_set(v___f_997_, 3, v___y_989_);
lean_closure_set(v___f_997_, 4, v___y_990_);
lean_closure_set(v___f_997_, 5, v___y_991_);
v___x_998_ = 1;
v___x_999_ = 0;
v___x_1000_ = lean_box(0);
v___x_1001_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_984_, v___x_998_, v___x_999_, v___x_998_, v___x_999_, v___x_1000_, v___f_997_, v_cleanupAnnotations_986_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
if (lean_obj_tag(v___x_1001_) == 0)
{
return v___x_1001_;
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_984_ = stack[0].m_obj;
lean_object* v_k_985_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_986_ = stack[2].m_num;
lean_object* v___y_987_ = stack[3].m_obj;
lean_object* v___y_988_ = stack[4].m_obj;
lean_object* v___y_989_ = stack[5].m_obj;
lean_object* v___y_990_ = stack[6].m_obj;
lean_object* v___y_991_ = stack[7].m_obj;
lean_object* v___y_992_ = stack[8].m_obj;
lean_object* v___y_993_ = stack[9].m_obj;
lean_object* v___y_994_ = stack[10].m_obj;
lean_object* v___y_995_ = stack[11].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_984_, v_k_985_, v_cleanupAnnotations_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg___boxed(lean_object* v_e_1011_, lean_object* v_k_1012_, lean_object* v_cleanupAnnotations_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1024_; lean_object* v_res_1025_; 
v_cleanupAnnotations_boxed_1024_ = lean_unbox(v_cleanupAnnotations_1013_);
v_res_1025_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1011_, v_k_1012_, v_cleanupAnnotations_boxed_1024_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
return v_res_1025_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_object* v_00_u03b1_1026_, lean_object* v_e_1027_, lean_object* v_k_1028_, uint8_t v_cleanupAnnotations_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1027_, v_k_1028_, v_cleanupAnnotations_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1027_ = stack[1].m_obj;
lean_object* v_k_1028_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1029_ = stack[3].m_num;
lean_object* v___y_1030_ = stack[4].m_obj;
lean_object* v___y_1031_ = stack[5].m_obj;
lean_object* v___y_1032_ = stack[6].m_obj;
lean_object* v___y_1033_ = stack[7].m_obj;
lean_object* v___y_1034_ = stack[8].m_obj;
lean_object* v___y_1035_ = stack[9].m_obj;
lean_object* v___y_1036_ = stack[10].m_obj;
lean_object* v___y_1037_ = stack[11].m_obj;
lean_object* v___y_1038_ = stack[12].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(lean_box(0), v_e_1027_, v_k_1028_, v_cleanupAnnotations_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_e_1043_, lean_object* v_k_1044_, lean_object* v_cleanupAnnotations_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1056_; lean_object* v_res_1057_; 
v_cleanupAnnotations_boxed_1056_ = lean_unbox(v_cleanupAnnotations_1045_);
v_res_1057_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0(v_00_u03b1_1042_, v_e_1043_, v_k_1044_, v_cleanupAnnotations_boxed_1056_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
return v_res_1057_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(lean_object* v___y_1058_, lean_object* v_transientCache_1059_, lean_object* v_funext_1060_, lean_object* v_a_x3f_1061_){
_start:
{
lean_object* v___x_1063_; lean_object* v_numSteps_1064_; lean_object* v_persistentCache_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
v___x_1063_ = lean_st_ref_take(v___y_1058_);
v_numSteps_1064_ = lean_ctor_get(v___x_1063_, 0);
v_persistentCache_1065_ = lean_ctor_get(v___x_1063_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; lean_object* v_unused_1077_; 
v_unused_1076_ = lean_ctor_get(v___x_1063_, 3);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v___x_1063_, 2);
lean_dec(v_unused_1077_);
v___x_1067_ = v___x_1063_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_persistentCache_1065_);
lean_inc(v_numSteps_1064_);
lean_dec(v___x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 3, v_funext_1060_);
lean_ctor_set(v___x_1067_, 2, v_transientCache_1059_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_numSteps_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_persistentCache_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_transientCache_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_funext_1060_);
v___x_1071_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_st_ref_put(v___y_1058_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1069_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1058_ = stack[0].m_obj;
lean_object* v_transientCache_1059_ = stack[1].m_obj;
lean_object* v_funext_1060_ = stack[2].m_obj;
lean_object* v_a_x3f_1061_ = stack[3].m_obj;
lean_object* v_res_1078_;
v_res_1078_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1058_, v_transientCache_1059_, v_funext_1060_, v_a_x3f_1061_);
stack->m_obj
 = v_res_1078_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0___boxed(lean_object* v___y_1079_, lean_object* v_transientCache_1080_, lean_object* v_funext_1081_, lean_object* v_a_x3f_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1079_, v_transientCache_1080_, v_funext_1081_, v_a_x3f_1082_);
lean_dec(v_a_x3f_1082_);
lean_dec(v___y_1079_);
return v_res_1084_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(lean_object* v_simpBody_1085_, lean_object* v_e_1086_, lean_object* v_xs_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_transientCache_1100_; lean_object* v___x_1101_; lean_object* v_funext_1102_; lean_object* v_a_1104_; lean_object* v___x_1115_; 
v___x_1099_ = lean_st_ref_get(v___y_1091_);
v_transientCache_1100_ = lean_ctor_get(v___x_1099_, 2);
lean_inc_ref(v_transientCache_1100_);
lean_dec(v___x_1099_);
v___x_1101_ = lean_st_ref_get(v___y_1091_);
v_funext_1102_ = lean_ctor_get(v___x_1101_, 3);
lean_inc_ref(v_funext_1102_);
lean_dec(v___x_1101_);
v___x_1115_ = l_Lean_Meta_Sym_shareCommon(v_b_1088_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = l___private_Lean_Meta_Sym_Simp_Lambda_0__Lean_Meta_Sym_Simp_simpLambda_x27_main(v_simpBody_1085_, v_e_1086_, v_xs_1087_, v_a_1116_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1134_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1134_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1134_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
lean_inc(v_a_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
v___x_1124_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1091_, v_transientCache_1100_, v_funext_1102_, v___x_1123_);
lean_dec_ref(v___x_1123_);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1124_, 0);
lean_dec(v_unused_1132_);
v___x_1126_ = v___x_1124_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v___x_1124_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v_a_1118_);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1118_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1117_, 1);
v_a_1104_ = v_a_1135_;
goto v___jp_1103_;
}
}
else
{
lean_object* v_a_1136_; 
lean_dec_ref(v_xs_1087_);
lean_dec_ref(v_e_1086_);
lean_dec_ref(v_simpBody_1085_);
v_a_1136_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1115_, 1);
v_a_1104_ = v_a_1136_;
goto v___jp_1103_;
}
v___jp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__0(v___y_1091_, v_transientCache_1100_, v_funext_1102_, v___x_1105_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___x_1106_, 0);
lean_dec(v_unused_1114_);
v___x_1108_ = v___x_1106_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v___x_1106_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 1);
lean_ctor_set(v___x_1108_, 0, v_a_1104_);
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1104_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_1085_ = stack[0].m_obj;
lean_object* v_e_1086_ = stack[1].m_obj;
lean_object* v_xs_1087_ = stack[2].m_obj;
lean_object* v_b_1088_ = stack[3].m_obj;
lean_object* v___y_1089_ = stack[4].m_obj;
lean_object* v___y_1090_ = stack[5].m_obj;
lean_object* v___y_1091_ = stack[6].m_obj;
lean_object* v___y_1092_ = stack[7].m_obj;
lean_object* v___y_1093_ = stack[8].m_obj;
lean_object* v___y_1094_ = stack[9].m_obj;
lean_object* v___y_1095_ = stack[10].m_obj;
lean_object* v___y_1096_ = stack[11].m_obj;
lean_object* v___y_1097_ = stack[12].m_obj;
lean_object* v_res_1137_;
v_res_1137_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(v_simpBody_1085_, v_e_1086_, v_xs_1087_, v_b_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
stack->m_obj
 = v_res_1137_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed(lean_object* v_simpBody_1138_, lean_object* v_e_1139_, lean_object* v_xs_1140_, lean_object* v_b_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1(v_simpBody_1138_, v_e_1139_, v_xs_1140_, v_b_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
return v_res_1152_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27(lean_object* v_simpBody_1153_, lean_object* v_e_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___f_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; 
lean_inc_ref(v_e_1154_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpLambda_x27___lam__1___boxed), 14, 2);
lean_closure_set(v___f_1165_, 0, v_simpBody_1153_);
lean_closure_set(v___f_1165_, 1, v_e_1154_);
v___x_1166_ = 0;
v___x_1167_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_Sym_Simp_simpLambda_x27_spec__0___redArg(v_e_1154_, v___f_1165_, v___x_1166_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1167_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpLambda_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_simpBody_1153_ = stack[0].m_obj;
lean_object* v_e_1154_ = stack[1].m_obj;
lean_object* v_a_1155_ = stack[2].m_obj;
lean_object* v_a_1156_ = stack[3].m_obj;
lean_object* v_a_1157_ = stack[4].m_obj;
lean_object* v_a_1158_ = stack[5].m_obj;
lean_object* v_a_1159_ = stack[6].m_obj;
lean_object* v_a_1160_ = stack[7].m_obj;
lean_object* v_a_1161_ = stack[8].m_obj;
lean_object* v_a_1162_ = stack[9].m_obj;
lean_object* v_a_1163_ = stack[10].m_obj;
lean_object* v_res_1168_;
v_res_1168_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v_simpBody_1153_, v_e_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
stack->m_obj
 = v_res_1168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda_x27___boxed(lean_object* v_simpBody_1169_, lean_object* v_e_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v_simpBody_1169_, v_e_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
return v_res_1181_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpLambda(lean_object* v_e_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLambda___closed__0));
v___x_1195_ = l_Lean_Meta_Sym_Simp_simpLambda_x27(v___x_1194_, v_e_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
return v___x_1195_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1183_ = stack[0].m_obj;
lean_object* v_a_1184_ = stack[1].m_obj;
lean_object* v_a_1185_ = stack[2].m_obj;
lean_object* v_a_1186_ = stack[3].m_obj;
lean_object* v_a_1187_ = stack[4].m_obj;
lean_object* v_a_1188_ = stack[5].m_obj;
lean_object* v_a_1189_ = stack[6].m_obj;
lean_object* v_a_1190_ = stack[7].m_obj;
lean_object* v_a_1191_ = stack[8].m_obj;
lean_object* v_a_1192_ = stack[9].m_obj;
lean_object* v_res_1196_;
v_res_1196_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
stack->m_obj
 = v_res_1196_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object* v_e_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_Sym_Simp_simpLambda(v_e_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
return v_res_1208_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
